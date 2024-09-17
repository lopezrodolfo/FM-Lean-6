# Isomorphisms and Equivalence Relations

This Lean project explores concepts related to isomorphisms, equivalence relations, and logical equivalence. It includes implementations of various mathematical structures and proofs.

## Author

Rodolfo Lopez

## Date

Fall 2022

## Installation

To run this project, you need to install Lean. The recommended way is to use elan, the Lean version manager:

1. Install elan:

   - On Unix-like systems (Linux, macOS):
     ```
     curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
     ```
   - On Windows:
     ```
     curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -sSf | powershell -c -
     ```

2. Restart your terminal or run `source ~/.profile` (or equivalent for your shell).

3. Install Lean:

   ```
   elan install leanprover/lean:stable
   ```

4. Verify the installation:
   ```
   lean --version
   ```

For more detailed instructions, visit the [Lean website](https://leanprover.github.io/lean4/doc/setup.html).

## Usage

Open the `hw6.lean` file in a Lean-compatible editor to view and evaluate the code.

## File Structure

- `hw6.lean`: Contains implementations of isomorphisms, equivalence relations, and related proofs

## Key Concepts

The project covers the following Lean concepts:

- Structures and typeclasses
- Isomorphisms and bijections
- Equivalence relations
- Logical equivalence
- Proofs using tactics

## Key Functions and Structures

- `iso`: Represents an isomorphism between two types
- `inverse_iso`: Reverses the direction of an isomorphism
- `compose_iso`: Composes two isomorphisms
- `bnot_iso`: Proves that boolean negation is an isomorphism
- `eqr`: Typeclass for equivalence relations
- `eq_is_eqr`: Proves that equality is an equivalence relation
- `eqr_iff`: Proves that logical equivalence is an equivalence relation on propositions
- `equiv_class`: Defines the equivalence class of an element
- `iso_eqc`: Proves that equivalent elements have isomorphic equivalence classes
