# VSAFECode

Gives a verified type-checker for SAFECode.

The SAFECode compiler is developed here:
[SAFECode](https://safecode.cs.illinois.edu/)


## Installation

1. Create the verified type-checker.
    ```
    cd formalization
    make
    cd ..
    ```
2. Extract and copy the verified type-checker.
    ```
    ./extract.sh
    ```
3. Create the type-checking tool that operates on SafeCode C.
    ```
    cd typechecker
    make
    cd ..
    ```
