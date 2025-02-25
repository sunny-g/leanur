# Leanur Development Guide

## Build/Test Commands
- Build the project: `lake build`
- Run the executable: `lake exe leanur`
- Check a single file: `lean path/to/file.lean`
- Run tests: `lake test`
- Run single test: `lean Test/path/to/test.lean`

## Code Style Guidelines
- **Imports**: Group imports by library. Import Lean standard library modules first, then project modules.
- **Formatting**: Follow standard Lean spacing - 2 spaces for indentation.
- **Types**: Always provide explicit type signatures for public definitions.
- **Naming**: 
  - Use camelCase for functions and variables (e.g., `nockNatLiteral`)
  - Use PascalCase for types and inductive constructors (e.g., `Noun`, `CompilerCtx`)
  - Use snake_case for module names
- **Documentation**: Document public functions with doc comments (`/-- ... -/`).
- **Error Handling**: Use `Option` type for operations that might fail.
- **Organization**: Group related functions in namespaces or sections.