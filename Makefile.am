include $(top_srcdir)/Makefile.tool.am

EXTRA_DIST = docs/trace-manual.xml

#----------------------------------------------------------------------------
# trace-<platform>
#----------------------------------------------------------------------------

noinst_PROGRAMS  = trace-@VGCONF_ARCH_PRI@-@VGCONF_OS@
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += trace-@VGCONF_ARCH_SEC@-@VGCONF_OS@
endif

TRACE_SOURCES_COMMON = trace_main.c

trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = \
	$(TRACE_SOURCES_COMMON)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_PRI@ \
	$(LINK) \
	$(trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS) \
	$(trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS)

if VGCONF_HAVE_PLATFORM_SEC
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = \
	$(TRACE_SOURCES_COMMON)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_SEC@ \
	$(LINK) \
	$(trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS) \
	$(trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS)
endif

#----------------------------------------------------------------------------
# vgpreload_trace-<platform>.so
#----------------------------------------------------------------------------

noinst_PROGRAMS += vgpreload_trace-@VGCONF_ARCH_PRI@-@VGCONF_OS@.so
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += vgpreload_trace-@VGCONF_ARCH_SEC@-@VGCONF_OS@.so
endif

if VGCONF_OS_IS_DARWIN
noinst_DSYMS = $(noinst_PROGRAMS)
endif

vgpreload_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_SOURCES      =
vgpreload_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CPPFLAGS     = \
        $(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
vgpreload_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CFLAGS       = \
        $(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@) $(AM_CFLAGS_PIC)
vgpreload_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_DEPENDENCIES = \
        $(LIBREPLACEMALLOC_@VGCONF_PLATFORM_PRI_CAPS@)
vgpreload_trace_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_LDFLAGS      = \
        $(PRELOAD_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@) \
        $(LIBREPLACEMALLOC_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)

if VGCONF_HAVE_PLATFORM_SEC
vgpreload_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_SOURCES      =
vgpreload_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_CPPFLAGS     = \
        $(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
vgpreload_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_CFLAGS       = \
        $(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) $(AM_CFLAGS_PIC)
vgpreload_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_DEPENDENCIES = \
        $(LIBREPLACEMALLOC_@VGCONF_PLATFORM_SEC_CAPS@)
vgpreload_trace_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_LDFLAGS      = \
        $(PRELOAD_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) \
        $(LIBREPLACEMALLOC_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
endif

