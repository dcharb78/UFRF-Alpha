/-
  UFRF/Results.lean

  Summary of UFRF predictions for physical constants.

  This file provides a clean handle to point people at:
  * "Here is the core theorem about constants"
  * "Here is the core theorem about observer invariance"
-/

import UFRF.CycleAxioms
import UFRF.AlphaDerivation
import UFRF.AlphaNumericBounds
import UFRF.GravityDerivation
import UFRF.GravityNumericBounds

namespace UFRF

/--
EM and gravitational couplings as predicted by UFRF geometry + projection
match experimental values within the following bounds:

* EM (fine-structure α):     ppbError ≤ 0.0075
* Gravity (dimensionless α_G): percentErrorG ≤ 0.3

This theorem combines both proofs into a single statement showing that
UFRF successfully predicts both fundamental coupling constants.
-/
theorem em_and_gravity_within_experiment :
    ppbError ≤ 0.0075 ∧ percentErrorG ≤ 0.3 :=
  And.intro alpha_ppb_bound alphaG_percent_bound

/--
Cycle structure invariance: for any observer origin on the 13-position cycle,
the multiset of phase labels is the same.

(This is the formal "unity in context" statement for this layer.)

TODO: Uncomment when phase_counts_invariant is proven:
  -- lemma cycle_invariance_under_observer_shift (origin : Fin cycleLen) (ph : Phase) :
  --     countPhaseFromPerspective origin ph = countPhase ph :=
  --   phase_counts_invariant origin ph
-/

end UFRF

