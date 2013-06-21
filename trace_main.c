/*--------------------------------------------------------------------*/
/*--- Valgrind tool to dump memory access traces.                  ---*/
/*--------------------------------------------------------------------*/

/* This file is part of Trace, a Valgrind tool to generate memory
   traces.  It is based off of the Lackey tool by Nicholas Nethercote.

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

// -----------------------------------------------------------------
// The output of trace looks like this:
// I10R800:8      # 0x10 instructions followed by a read of 0x8
//                # bytes at 0x800
// I4Wabc0:4      # 0x4 instructions followed by a read of 0x4
//                # bytes at 0xabc0
// IaM1248:1      # 0xa instructions followed by a read of 0x1
//                # byte at 0x1248
//
// This tool differs from Lackey in that it dumps instruction counts
// and ignores instruction data.  It comes with the same caveats as
// Lackey regarding the quality of the traces.

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"

typedef IRExpr IRAtom;

typedef enum {
   Event_Ir, Event_Dr, Event_Dw, Event_Dm
} EventKind;

typedef struct {
   EventKind  ekind;
   IRAtom*    addr;
   Int        size;
} Event;

/* Region used for tracking memory allocations. */
typedef struct AddressRegion {
   long offset;
   long start;
   long size;
   struct AddressRegion *next;
} AddressRegion;

/* Data used to track the total amount of memory referenced. */
typedef struct AddressRange {
   long start;
   long size;
   struct AddressRange *next;
} AddressRange;

/* Up to this many unnotified events are allowed.  Must be at least two,
   so that reads and writes to the same address can be merged into a modify.
   Beyond that, larger numbers just potentially induce more spilling due to
   extending live ranges of address temporaries. */
#define N_EVENTS 4

/* Maintain an ordered list of memory events that are outstanding, in
   the sense that no IR has yet been generated to do the relevant
   helper calls.  The SB is scanned top to bottom and memory events
   are added to the end of the list, merging with the most recent
   notified event where possible (Dw immediately following Dr and
   having the same size and EA can be merged).

   This merging is done so that for architectures which have
   load-op-store instructions (x86, amd64), the instr is treated as if
   it makes just one memory reference (a modify), rather than two (a
   read followed by a write at the same address).

   At various points the list will need to be flushed, that is, IR
   generated from it.  That must happen before any possible exit from
   the block (the end, or an IRStmt_Exit).  Flushing also takes place
   when there is no space to add a new event.

   If we require the simulation statistics to be up to date with
   respect to possible memory exceptions, then the list would have to
   be flushed before each memory reference.  That's a pain so we don't
   bother.

   Flushing the list consists of walking it start to end and emitting
   instrumentation IR for each event, in the order in which they
   appear.  */

static Bool  clo_all_refs = True;
static Bool  clo_instructions = True;
static Bool  clo_references = True;
static Bool  clo_stats = False;
static Event events[N_EVENTS];
static Int   events_used = 0;
static Int   instr_count = 0;

static AddressRegion *regions = NULL;
static AddressRange  *ranges  = NULL;
static long watermark = 0;

static char check_overlap(const AddressRange *ap, const AddressRange *bp)
{
   const long a1 = ap->start;
   const long a2 = ap->start + ap->size;
   const long b1 = bp->start;
   const long b2 = bp->start + bp->size;

   if(a1 <= b1 && a2 >= b1) {
      /* a1 b1 a2 */
      return 1;
   }
   if(b1 <= a1 && b2 >= a1) {
      /* b1 a1 b2 */
      return 1;
   }
   return 0;
}

static void combine_ranges(const AddressRange *rp, AddressRange *tp)
{
   long end;
   end = rp->start + rp->size;
   if(tp->start + tp->size > end) {
      end = tp->start + tp->size;
   }
   if(rp->start < tp->start) {
      tp->start = rp->start;
   }
   tp->size = end - tp->start;
}

static void add_reference(Addr ptr, SizeT size)
{
   const long temp = ptr;
   AddressRange *rp;
   AddressRange *tp;
   char updated;

   /* Check if a range including this address already exists. */
   for(rp = ranges; rp; rp = rp->next) {
      if(temp >= rp->start && temp < rp->start + rp->size) {
         return;
      }
   }

   /* Does not already exist; insert a new region. */
   rp = VG_(malloc)("add_reference", sizeof(AddressRange));
   rp->next = ranges;
   ranges = rp;
   rp->start = temp;
   rp->size = size;

   /* Coalesce ranges. */
   do {
      updated = 0;
      rp = ranges;
      if(rp) {
         for(tp = rp->next; tp; tp = tp->next) {
            if(check_overlap(tp, rp)) {
               updated = 1;
               ranges = ranges->next;
               combine_ranges(rp, tp);
               VG_(free)(rp);
            }
         }
      }
   } while(updated);

}

static long get_total_size(void)
{
   long size = 0;
   AddressRange *rp;
   for(rp = ranges; rp; rp = rp->next) {
      size += rp->size;
   }
   return size;
}

static void free_ranges(void)
{
   AddressRange *rp;
   while(ranges) {
      rp = ranges->next;
      VG_(free)(ranges);
      ranges = rp;
   }
}

static void add_region(void *ptr, SizeT size)
{
   if(!clo_all_refs) {
      AddressRegion *rp = VG_(malloc)("add_region", sizeof(AddressRegion));
      rp->start   = (long)ptr;
      rp->size    = (long)size;
      rp->offset  = watermark;
      rp->next    = regions;
      regions     = rp;
      watermark += ((long)size + 7) & ~7;
   }
}

static void remove_region(void *ptr)
{
   if(!clo_all_refs) {
      AddressRegion **rp = &regions;
      const long temp = (long)ptr;
      while(*rp) {
         if(temp >= (*rp)->start && temp < ((*rp)->start + (*rp)->size)) {
            AddressRegion *tp = *rp;
            *rp = (*rp)->next;
            VG_(free)(tp);
            return;
         }
         rp = &(*rp)->next;
      }
      VG_(printf)("trace: ERROR: region not found\n");
   }
}

static long get_offset(Addr ptr)
{
   if(clo_all_refs) {
      return ptr;
   } else {
      AddressRegion *rp;
      for(rp = regions; rp; rp = rp->next) {
         if(ptr >= rp->start && ptr < rp->start + rp->size) {
            return ptr - rp->start + rp->offset;
         }
      }
      return -1;
   }
}

static void *trace_malloc(ThreadId tid, SizeT n)
{
   void *ptr = VG_(malloc)("trace_malloc", n);
   add_region(ptr, n);
   return ptr;
}

static void *trace_builtin_new(ThreadId tid, SizeT n)
{
   void *ptr = VG_(malloc)("trace_builtin_new", n);
   add_region(ptr, n);
   return ptr;
}

static void *trace_builtin_vec_new(ThreadId tid, SizeT n)
{
   void *ptr = VG_(malloc)("trace_builtin_vec_new", n);
   add_region(ptr, n);
   return ptr;
}

static void *trace_memalign(ThreadId tid, SizeT align, SizeT n)
{
   void *ptr;
   long p = (long)VG_(malloc)("trace_memalign", n + align);
   p += align - (p % align);
   ptr = (void*)p;
   add_region(ptr, n);
   return ptr;
}

static void *trace_calloc(ThreadId tid, SizeT nmem, SizeT size1)
{
   void *ptr = VG_(calloc)("trace_calloc", nmem, size1);
   add_region(ptr, size1 * nmem);
   return ptr;
}

static void trace_free(ThreadId tid, void *p)
{
   remove_region(p);
   return VG_(free)(p);
}

static void trace_builtin_delete(ThreadId tid, void *p)
{
   remove_region(p);
   return VG_(free)(p);
}

static void trace_builtin_vec_delete(ThreadId tid, void *p)
{
   remove_region(p);
   return VG_(free)(p);
}

static void *trace_realloc(ThreadId tid, void *p, SizeT new_size)
{
   remove_region(p);
   p = VG_(realloc)("trace_realloc", p, new_size);
   add_region(p, new_size);
   return p;
}

static SizeT trace_malloc_usable_size(ThreadId tid, void *p)
{
   return VG_(malloc_usable_size)(p);
}

static VG_REGPARM(2) void trace_instr(Addr addr, SizeT size)
{
   instr_count += 1;
}

static VG_REGPARM(2) void trace_load(Addr addr, SizeT size)
{
   const long offset = get_offset(addr);
   if(offset != -1) {
      if(clo_instructions && instr_count > 0) {
         VG_(printf)("I%x", instr_count);
         instr_count = 0;
      }
      if(clo_references) {
         VG_(printf)("R%lx:%lx\n", offset, size);
      }
      if(clo_stats) {
         add_reference(addr, size);
      }
   }
}

static VG_REGPARM(2) void trace_store(Addr addr, SizeT size)
{
   const long offset = get_offset(addr);
   if(offset != -1) {
      if(clo_instructions && instr_count > 0) {
         VG_(printf)("I%x", instr_count);
         instr_count = 0;
      }
      if(clo_references) {
         VG_(printf)("W%lx:%lx\n", offset, size);
      }
      if(clo_stats) {
         add_reference(addr, size);
      }
   }
}

static VG_REGPARM(2) void trace_modify(Addr addr, SizeT size)
{
   const long offset = get_offset(addr);
   if(offset != -1) {
      if(clo_instructions && instr_count > 0) {
         VG_(printf)("I%x", instr_count);
         instr_count = 0;
      }
      if(clo_references) {
         VG_(printf)("M%lx:%lx\n", offset, size);
      }
      if(clo_stats) {
         add_reference(addr, size);
      }
   }
}

static void flushEvents(IRSB *sb)
{
   Int i;

   for(i = 0; i < events_used; i++) {

      Char      *helperName;
      void      *helperAddr;
      IRExpr   **argv;
      IRDirty   *di;
      Event     *ev = &events[i];

      switch (ev->ekind) {
         case Event_Ir:
            helperName = "trace_instr";
            helperAddr =  trace_instr; 
            break;

         case Event_Dr:
            helperName = "trace_load";
            helperAddr =  trace_load;
            break;

         case Event_Dw:
            helperName = "trace_store";
            helperAddr =  trace_store;
            break;

         case Event_Dm:
            helperName = "trace_modify";
            helperAddr =  trace_modify;
            break;

         default:
            tl_assert(0);
            break;
      }

      // Add the helper.
      argv = mkIRExprVec_2(ev->addr, mkIRExpr_HWord(ev->size));
      di   = unsafeIRDirty_0_N(2, 
                               helperName,
                               VG_(fnptr_to_fnentry)(helperAddr),
                               argv);
      addStmtToIRSB(sb, IRStmt_Dirty(di));
   }

   events_used = 0;
}

static void addEvent_Ir(IRSB *sb, IRAtom *iaddr, UInt isize)
{
   Event *evt;
   if(events_used == N_EVENTS) {
      flushEvents(sb);
   }
   evt = &events[events_used];
   evt->ekind = Event_Ir;
   evt->addr  = iaddr;
   evt->size  = isize;
   events_used += 1;
}

static void addEvent_Dr(IRSB *sb, IRAtom *daddr, Int dsize)
{
   Event *evt;
   if(events_used == N_EVENTS) {
      flushEvents(sb);
   }
   evt = &events[events_used];
   evt->ekind = Event_Dr;
   evt->addr  = daddr;
   evt->size  = dsize;
   events_used += 1;
}

static void addEvent_Dw(IRSB *sb, IRAtom *daddr, Int dsize)
{
   Event *evt;

   // Attempt to merge this write with the preceding read.
   if(events_used > 0) {
      Event *lastEvt = &events[events_used - 1];
      if(   lastEvt->ekind == Event_Dr
         && lastEvt->size  == dsize
         && eqIRAtom(lastEvt->addr, daddr)) {
         lastEvt->ekind = Event_Dm;
         return;
      }
   }

   // Cannot merge.
   if(events_used == N_EVENTS) {
      flushEvents(sb);
   }
   evt = &events[events_used];
   evt->ekind = Event_Dw;
   evt->size  = dsize;
   evt->addr  = daddr;
   events_used += 1;
}

static void trace_post_clo_init(void)
{
}

static
IRSB* trace_instrument(VgCallbackClosure* closure,
                       IRSB* sbIn, 
                       VexGuestLayout* layout, 
                       VexGuestExtents* vge,
                       IRType gWordTy, IRType hWordTy )
{
   Int        i;
   IRSB      *sbOut;
   IRTypeEnv *tyenv = sbIn->tyenv;

   if(gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   /* Set up SB */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   /* Copy verbatim any IR preamble preceding the first IMark */
   i = 0;
   while(i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      addStmtToIRSB(sbOut, sbIn->stmts[i]);
      i += 1;
   }

   events_used = 0;
   for(; i < sbIn->stmts_used; i++) {

      IRStmt *st = sbIn->stmts[i];
      if(!st || st->tag == Ist_NoOp) {
         continue;
      }

      switch (st->tag) {
         case Ist_NoOp:
         case Ist_AbiHint:
         case Ist_Put:
         case Ist_PutI:
         case Ist_MBE:
            addStmtToIRSB(sbOut, st);
            break;

         case Ist_IMark:
            addEvent_Ir(sbOut, mkIRExpr_HWord((HWord)st->Ist.IMark.addr),
                        st->Ist.IMark.len);
            addStmtToIRSB(sbOut, st);
            break;

         case Ist_WrTmp: {
            IRExpr *data = st->Ist.WrTmp.data;
            if(data->tag == Iex_Load) {
               addEvent_Dr(sbOut, data->Iex.Load.addr,
                           sizeofIRType(data->Iex.Load.ty));
            }
            addStmtToIRSB(sbOut, st);
            break;
         }

         case Ist_Store: {
            IRExpr *data  = st->Ist.Store.data;
            addEvent_Dw(sbOut, st->Ist.Store.addr,
                        sizeofIRType(typeOfIRExpr(tyenv, data)));
            addStmtToIRSB(sbOut, st);
            break;
         }

         case Ist_Dirty: {
            IRDirty *d = st->Ist.Dirty.details;
            if(d->mFx != Ifx_None) {
               if(d->mFx == Ifx_Read || d->mFx == Ifx_Modify) {
                  addEvent_Dr(sbOut, d->mAddr, d->mSize);
               }
               if(d->mFx == Ifx_Write || d->mFx == Ifx_Modify) {
                  addEvent_Dw(sbOut, d->mAddr, d->mSize);
               }
            }
            addStmtToIRSB(sbOut, st);
            break;
         }

         case Ist_CAS: {
            IRCAS *cas      = st->Ist.CAS.details;
            IRType dataTy   = typeOfIRExpr(tyenv, cas->dataLo);
            Int    dataSize = sizeofIRType(dataTy);
            if(cas->dataHi != NULL) {
               dataSize *= 2; /* doubleword-CAS */
            }
            addEvent_Dr(sbOut, cas->addr, dataSize);
            addEvent_Dw(sbOut, cas->addr, dataSize);
            addStmtToIRSB(sbOut, st);
            break;
         }

         case Ist_LLSC: {
            IRType dataTy;
            if(st->Ist.LLSC.storedata == NULL) {
               dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
               addEvent_Dr(sbOut, st->Ist.LLSC.addr,
                           sizeofIRType(dataTy) );
            } else {
               dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
               addEvent_Dw(sbOut, st->Ist.LLSC.addr,
                           sizeofIRType(dataTy));
            }
            addStmtToIRSB(sbOut, st);
            break;
         }

         case Ist_Exit:
            flushEvents(sbOut);
            addStmtToIRSB(sbOut, st);
            break;

         default:
            tl_assert(0);
            break;
      }
   }

   flushEvents(sbOut);

   return sbOut;
}

static void trace_fini(Int exitcode)
{
   if(clo_instructions && instr_count > 0) {
      VG_(printf)("I%x\n", instr_count);
      instr_count = 0;
   }
   if(clo_stats) {
      const long size = get_total_size();
      VG_(printf)("Total bytes accessed: %ld\n", size);
      free_ranges();
   }
}

static Bool trace_process_cmd_line_option(Char *arg)
{
   if      VG_BOOL_CLO(arg, "--all-refs", clo_all_refs) {}
   else if VG_BOOL_CLO(arg, "--instructions", clo_instructions) {}
   else if VG_BOOL_CLO(arg, "--access-stats", clo_stats) {}
   else if VG_BOOL_CLO(arg, "--references", clo_references) {}
   else
      return False;
   return True;
}

static void trace_print_usage(void)
{
   VG_(printf)(
"    --all-refs=no|yes     track all memory references [yes]\n"
"    --instructions=no|yes track instruction counts [yes]\n"
"    --references=no|yes   track references [yes]\n"
"    --access_stats=yes|no track access stats [no]\n"
   );
}

static void trace_print_debug_usage(void)
{
   VG_(printf)(
"    (none)\n"
   );
}

static void trace_pre_clo_init(void)
{
   VG_(details_name)("Trace");
   VG_(details_version)(NULL);
   VG_(details_description)("Valgrind tool to generate memory traces");

   VG_(details_copyright_author)(
      "Copyright (C) 2013, and GNU GPL'd, by Joe Wingbermuehle.");

   VG_(details_bug_reports_to)(VG_BUGS_TO);
   VG_(details_avg_translation_sizeB)(200);

   VG_(basic_tool_funcs)(trace_post_clo_init, trace_instrument, trace_fini);

   VG_(needs_malloc_replacement)(trace_malloc,
                                 trace_builtin_new,
                                 trace_builtin_vec_new,
                                 trace_memalign,
                                 trace_calloc,
                                 trace_free,
                                 trace_builtin_delete,
                                 trace_builtin_vec_delete,
                                 trace_realloc,
                                 trace_malloc_usable_size,
                                 16
   );

   VG_(needs_command_line_options)(trace_process_cmd_line_option,
                                   trace_print_usage,
                                   trace_print_debug_usage);

}

VG_DETERMINE_INTERFACE_VERSION(trace_pre_clo_init)

