# Jacobi contribution CI

This harness checks a fixed commit of the jacobi-formula branch against the upstream commit in source.json. The source checkout is independent of this harness branch. It uses GitHub-hosted Linux runners and the pinned Lean toolchain.

Checks: strict build of the three contribution modules and their dependencies; downstream clients covering norm-free and Frobenius derivatives, composition, singular and empty matrices, incomplete fields, and generic trace coefficients; the axiom closure of every declaration introduced by the modules (allowing only propext, Classical.choice and Quot.sound); Mathlib environment and style linters; mk_all; patch whitespace and unchanged source hashes.

This is scoped contribution CI. Mathlib's complete upstream CI, including its full repository test suites, is run when a PR is submitted upstream.
