To build:
Run make in the current directory

To use:
check.byte <inputfile>.bc

Note that we are using a modified version of the SAFECode compiler that further
instruments the LLVM bitcode. You can find instructions on how to build the
modified version in the directory llvmpass. Alternatively, we have included
preinstrumented bitcode files in the test directory.
