# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the UC Berkeley CS 263 "Reasoning about Programs" course repository (Spring 2026). It uses **Lean 4** for formal verification and theorem proving, based on the "Hitchhiker's Guide to Logical Verification" textbook.

## Build Commands

```bash
# Build the main library
lake build LoVe.LoVelib

# Build everything
lake build

# Update dependencies
lake update
```

The project uses **Lake** (Lean's package manager) with Lean v4.26.0.

## Project Structure

- **LoVe/**: Main course materials
  - `LoVelib.lean`: Core library with proofs, macros, and shared definitions
  - `LoVe0X_*_Demo.lean`: Lecture demonstrations
  - `LoVe0X_*_ExerciseSheet.lean`: Student exercises
- **Homework/**: Student assignments with `@[autogradedDef]` annotations for Gradescope

## Key Dependencies

- **mathlib4**: Community mathematics library (v4.26.0)
- **autograder**: Lean 4 autograder for homework grading

## Lean Conventions in This Codebase

- All files use `namespace LoVe`
- `set_option autoImplicit false` is standard
- Homework files import `AutograderLib` and `LoVe.LoVelib`
- Exercise sheets import their corresponding demo files
- Uses structured proof syntax with custom `fix` and `assume` macros defined in LoVelib

## Course Topics

1. **LoVe01**: Types and Terms - basic type theory, combinators (I, K, C)
2. **LoVe02**: Programs and Theorems - inductive types, functions, properties
3. **LoVe03**: Backward Proofs - tactics (intro, apply, exact), propositional logic
