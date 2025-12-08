-- UFRF/Params.lean
/-
  UFRF core parameters in minimal form.

  This file does **not** try to prove deep geometry yet.
  It just fixes:
    • φ  : golden ratio
    • 13 : cycle length (from CycleAxioms)
    • 10 : REST position (1-based, corresponds to restIndex in CycleAxioms)

  Later you can replace the axioms with proper proofs or
  with derivations from TripleManifold / CylinderFlow.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import UFRF.CycleAxioms

namespace UFRF

noncomputable section
open Real

/-- Golden ratio φ = (1 + √5)/2. -/
def phi : ℝ := (1 + sqrt 5) / 2

/-- Axiom: φ satisfies the usual golden-ratio equation φ² = φ + 1. -/
axiom phi_golden : phi ^ 2 = phi + 1

/-- Axiom: φ > 1. -/
axiom phi_gt_one : 1 < phi

/-- Length of the fundamental UFRF cycle (13 positions).
    
    This re-exports `cycleLen` from `CycleAxioms` for backward compatibility.
    The cycle structure is now formally defined in `CycleAxioms.lean`.
-/
-- Re-export cycleLen from CycleAxioms (already defined there)

/-- REST / √φ enhancement position in the 13-cycle (1-based).
    
    This is kept for backward compatibility. The 0-based version is
    `restIndex : Fin cycleLen` in `CycleAxioms.lean`.
    
    Conversion: restPhase = restIndex.val + 1 = 9 + 1 = 10
-/
def restPhase : ℕ := 10

/-- Conversion lemma: restPhase (1-based) = restIndex.val + 1 (0-based). -/
lemma restPhase_eq_restIndex_plus_one : restPhase = restIndex.val + 1 := by
  rfl

/-- Sanity check: REST is inside the cycle. -/
lemma restPhase_lt_cycle : restPhase < cycleLen := by
  -- 10 < 13 is decidable arithmetics
  decide

end
