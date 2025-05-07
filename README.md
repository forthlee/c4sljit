# c4sljit - JIT-Enhanced C Compiler

## Overview
`c4sljit` is a modified version of the `c4` compiler, originally developed by Robert Swierczek ([rswier/c4](https://github.com/rswier/c4)). The original `c4` is a minimal C compiler implemented in four functions, using a simple virtual machine (VM) for code execution. This project replaces the VM with a Just-In-Time (JIT) compilation approach using the [SLJIT](https://github.com/zherczeg/sljit) library, aiming to improve performance by generating native machine code at runtime.

## Features
- **JIT Compilation**: Utilizes SLJIT to generate native machine code, replacing the interpretive VM of the original `c4`.
- **Minimal C Subset**: Supports a subset of C, including basic types (`int`, `char`), pointers, functions, conditionals, loops, and standard library functions (`printf`, `malloc`, etc.).
- **Source Debugging**: Includes an optional `-s` flag to print source code and generated intermediate code for debugging.
- **Lightweight**: Retains the simplicity and small footprint of the original `c4` compiler.

## Prerequisites
To build and run `c4sljit`, you need:
- A C compiler (e.g., `gcc`)
- The SLJIT library (included in the `sljit_src` directory or available at [zherczeg/sljit](https://github.com/zherczeg/sljit))
- A POSIX-compatible system (e.g., Linux, macOS)

## Building
1. Clone the repository:
   ```bash
   git clone https://github.com/forthlee/c4sljit.git
   cd c4sljit
   ```
2. Compile the code using the provided command:
   ```bash
   gcc -DSLJIT_CONFIG_AUTO=1 -I./sljit_src ./sljit_src/sljitLir.c c4sljit.c -o c4sljit
   ```
   - The `-DSLJIT_CONFIG_AUTO=1` flag enables automatic configuration for SLJIT.
   - Ensure the `sljit_src` directory contains the SLJIT source files.

## Usage
Run the compiler with a C source file:
```bash
./c4sljit [-s] <source_file.c>
```
- **`-s`**: Optional flag to print the source code and intermediate code during compilation for debugging.
- `<source_file.c>`: The input C source file to compile and execute.

Example:
```bash
./c4sljit example.c
```
To debug:
```bash
./c4sljit -s example.c
```

## How It Works
1. **Parsing**: The compiler reads the input C source, tokenizes it, and builds a symbol table.
2. **Code Generation**: It generates intermediate code (opcodes) similar to the original `c4` VM, but these are translated into SLJIT instructions.
3. **JIT Compilation**: SLJIT converts the intermediate code into native machine code, handling jumps, calls, and arithmetic operations.
4. **Execution**: The generated machine code is executed directly, with results returned to the user.

## Differences from Original c4
- **Execution Model**: Replaces the VM with SLJIT-based JIT compilation for faster execution.
- **Code Emission**: Uses SLJIT's API to emit native instructions instead of interpreting opcodes.
- **Stack Management**: Implements stack operations (`_push`, `_pop`, `_drop`) as SLJIT-compatible functions.
- **System Calls**: Maps system functions (`open`, `read`, `printf`, etc.) to SLJIT calls.

## Limitations
- Inherits the limitations of `c4`, such as support for only a subset of C (no structs, unions, or floating-point types).
- SLJIT-specific constraints, such as platform-dependent code generation.
- Error handling is minimal, with basic error messages for syntax or compilation issues.

## Example
An example C program (`example.c`):
```c
int main() {
    printf("Hello, JIT World!\n");
    return 0;
}
```
Compile and run:
```bash
./c4sljit example.c
```
Output:
```
Hello, JIT World!
```
