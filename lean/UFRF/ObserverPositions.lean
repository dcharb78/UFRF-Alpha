/-
  UFRF/ObserverPositions.lean

  Defines where EM and Gravity observers sit in the 13-cycle.

  This provides formal handles to talk about "where Alpha/Gravity live
  in the cycle" without polluting the core proofs.
-/

import UFRF.CycleAxioms
import UFRF.Params

namespace UFRF

/-- EM observer position in the 13-cycle.

    This represents where the electromagnetic (fine structure constant)
    observer sits. Position 8 corresponds to the "harmonize" phase.
-/
def emObserverIndex : Fin cycleLen := ⟨8, by decide⟩

/-- EM observer phase: the phase label at the EM observer position. -/
def emObserverPhase : Phase := phaseOf emObserverIndex

/-- EM observer sits at the harmonize phase. -/
lemma emObserverPhase_is_harmonize :
    emObserverPhase = Phase.harmonize := by
  unfold emObserverPhase emObserverIndex
  -- emObserverIndex = 8, and phaseOf 8 = harmonize (from phaseOf definition)
  rfl

/-- Gravity observer position in the 13-cycle.

    This represents where the gravitational coupling observer sits.
    Position 9 corresponds to the "rest" phase (same as restIndex).
-/
def gravityObserverIndex : Fin cycleLen := restIndex

/-- Gravity observer phase: the phase label at the gravity observer position. -/
def gravityObserverPhase : Phase := phaseOf gravityObserverIndex

/-- Gravity observer sits at the rest phase. -/
lemma gravityObserverPhase_is_rest :
    gravityObserverPhase = Phase.rest := by
  unfold gravityObserverPhase gravityObserverIndex
  exact phaseOf_restIndex

end UFRF

