
Trace
==============================================================================

This is a simple Valgrind tool based on Lackey to gather memory traces.

The output of trace looks like this:

<pre>
I10R800:8      # 0x10 instructions followed by a read of 0x8
               # bytes at 0x800
I4Wabc0:4      # 0x4 instructions followed by a read of 0x4
               # bytes at 0xabc0
IaM1248:1      # 0xa instructions followed by a read of 0x1
               # byte at 0x1248
</pre>

This tool differs from Lackey in that it dumps instruction counts
and ignores instruction data.  It comes with the same caveats as
Lackey regarding the quality of the traces.

Currently, there is only a single option:

<pre>
--all-refs=no|yes
<pre>

This determines whether all data memory accesses are logged ("yes", the
default) or if only accesses to data that was explicitly allocated by the
program ("no").

