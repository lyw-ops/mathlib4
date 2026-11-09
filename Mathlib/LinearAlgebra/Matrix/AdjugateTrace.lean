/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace identities for the adjugate

Summing determinants obtained by replacing one row, or one column, of `A` with the
corresponding row or column of `B` gives `trace (adjugate A * B)`.
These algebraic forms of Jacobi's formula work over any commutative ring,
including singular matrices and empty index types.

## Main results

* `Matrix.sum_det_updateRow_eq_trace_adjugate_mul`: the row-replacement identity.
* `Matrix.sum_det_updateCol_eq_trace_adjugate_mul`: the column-replacement identity.

## Implementation details

The proofs are adapted from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/blob/ed6c0aa3acc0a3cb56901dc406167cdbad593f59/TauCeti/LinearAlgebra/Matrix/Adjugate/Basic.lean).
-/

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The sum of determinants obtained by replacing a row is the trace of the
adjugate times the matrix of replacement rows. -/
theorem sum_det_updateRow_eq_trace_adjugate_mul (A B : Matrix n n R) :
    ∑ i, (A.updateRow i (B i)).det = (adjugate A * B).trace := by
  simp only [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, trace,
    diag_apply, Matrix.mul_apply, mulVec, dotProduct, transpose_apply]
  exact Finset.sum_comm

/-- The sum of determinants obtained by replacing a column is the trace of the
adjugate times the matrix of replacement columns. -/
theorem sum_det_updateCol_eq_trace_adjugate_mul (A B : Matrix n n R) :
    ∑ j, (A.updateCol j fun i ↦ B i j).det = (adjugate A * B).trace := by
  simp only [← cramer_apply, cramer_eq_adjugate_mulVec, trace, diag_apply, Matrix.mul_apply, mulVec,
    dotProduct]

end Matrix
