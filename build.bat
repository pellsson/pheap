@echo off
setlocal ENABLEDELAYEDEXPANSION

set OBJDIR=obj
set CC=cl.exe
set CXX=cl.exe
set LD=link.exe
set AR=lib.exe

set CFLAGS=/D_CRT_SECURE_NO_WARNINGS /nologo /W4 /O2
set ARFLAGS=/NOLOGO

set TEST_DEFS=/DPHEAP_TEST /DPHEAP_USE_GLOBAL_HEAP=1


set VS_MAJOR=

for /f "delims=. tokens=1" %%a in ("%VSCMD_VER%") do (
	set VS_MAJOR=%%a
)

if not defined VS_MAJOR (
	echo You must run this batchfile from a Visual Studo Developer Console.
	goto failure
)

echo Visual Studio Developer Console detected ^(Version: %VS_MAJOR%^).

mkdir %OBJDIR% 2> NUL

erase /Q /F %OBJDIR%\*

echo Building pheap static library
%CC% %CFLAGS% /Fo:%OBJDIR%/pheap.obj pheap.c /c || goto failure
%AR% %ARFLAGS% /OUT:pheap.lib %OBJDIR%\pheap.obj || goto failure

echo Building pheap tests
%CC% %TEST_DEFS% %CFLAGS% pheap.c /Fo:%OBJDIR%/pheap-test.obj /c || goto failure
%CXX% %TEST_DEFS% %CFLAGS% /EHsc test/test.cpp /Fo:%OBJDIR%/test.obj /c || goto failure
%LD% /NOLOGO kernel32.lib user32.lib %OBJDIR%/test.obj %OBJDIR%/pheap-test.obj /OUT:pheap-test.exe || goto failure

echo Build was successful!
exit /B 0

:failure
echo The build has failed.
exit /B 1337