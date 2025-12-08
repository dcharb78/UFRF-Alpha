-- UFRF/Params.lean
/-
  UFRF core parameters in minimal form.

  This file does **not** try to prove deep geometry yet.
  It just fixes:
    • φ  : golden ratio
    • 13 : cycle length
    • 10 : REST position

  Later you can replace the axioms with proper proofs or
  with derivations from TripleManifold / CylinderFlow.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace UFRF

noncomputable section
open Real

/-- Golden ratio φ = (1 + √5)/2. -/
def phi : ℝ := (1 + sqrt 5) / 2

/-- Axiom: φ satisfies the usual golden-ratio equation φ² = φ + 1. -/
axiom phi_golden : phi ^ 2 = phi + 1

/-- Axiom: φ > 1. -/
axiom phi_gt_one : 1 < phi

/-- Length of the fundamental UFRF cycle (13 positions). -/
def cycleLen : ℕ := 13

/-- REST / √φ enhancement position in the 13-cycle. -/
def restPhase : ℕ := 10

/-- Sanity check: REST is inside the cycle. -/
lemma restPhase_lt_cycle : restPhase < cycleLen := by
  -- 10 < 13 is decidable arithmetics
  decide

end
