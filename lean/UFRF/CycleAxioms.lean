/-
  UFRF/CycleAxioms.lean

  Shared combinatorial / geometric structure used across UFRF-Alpha,
  UFRF-Gravity, and (later) UFRF-Moonshine.

  This file is intentionally "physics-neutral":

  * It defines a 13-position cycle with 5 phase types.
  * It distinguishes a "REST" phase at a specific index.
  * It defines how to "rotate" the cycle to represent different observer
    perspectives, so that any position can be taken as the origin.

  All physical interpretation (EM, gravity, Monster, etc.) lives in
  separate files that IMPORT these axioms, not here.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

namespace UFRF

/-- Phase labels in one 13-position cycle.

    The names are intentionally generic:

    * `seed`      – initial / seeding phase
    * `amplify`   – growth / amplification phase
    * `harmonize` – balancing / interference phase
    * `rest`      – distinguished "rest" / equilibrium phase
    * `new`       – completion / transition to next cycle
-/
inductive Phase : Type
  | seed
  | amplify
  | harmonize
  | rest
  | new
deriving DecidableEq, Repr

open Phase

/-- Length of the fundamental cycle. -/
def cycleLen : ℕ := 13

/-- Index of the distinguished REST point in the 13-position cycle.

    We work 0-based in Lean, so:

      * positions are 0,1,…,12 (type `Fin 13`)
      * REST is at index 9  (corresponding to "position 10" in 1-based language)
-/
def restIndex : Fin cycleLen := ⟨9, by decide⟩

/-- Phase assignment for each position in the 13-cycle.

    0,1,2   → seed
    3,4,5   → amplify
    6,7,8   → harmonize
    9       → rest
    10,11,12 → new
-/
def phaseOf (i : Fin cycleLen) : Phase :=
  match (i : ℕ) with
  | 0 | 1 | 2   => seed
  | 3 | 4 | 5   => amplify
  | 6 | 7 | 8   => harmonize
  | 9          => rest
  | _          => new

/-- Sanity check: `restIndex` is indeed labeled as `Phase.rest`. -/
lemma phaseOf_restIndex : phaseOf restIndex = Phase.rest := by
  -- restIndex = 9, which matches the `9` case in `phaseOf`
  rfl

/-- A simple helper: the "seed" positions are exactly 0,1,2. -/
lemma phaseOf_seed_positions (i : Fin cycleLen) :
    phaseOf i = Phase.seed ↔ (i : ℕ) ≤ 2 := by
  -- This is a convenient characterization used in some constructions.
  -- You can refine this later if you need exact equivalences per index.
  cases i using Fin.cases <;> simp [phaseOf]

/-!
## Observer perspective: rotating the cycle

To express "unity in context" / "all is one from different perspectives",
we formalize the idea that any position of the 13-cycle can be taken as
a new "origin" by *rotating* the labels.

*Mathematically*: this is just a cyclic shift on `Fin 13`.
-/

/-- Cyclic rotation on the 13-position cycle.

    `rotate offset i` means "move `i` forward by `offset` steps modulo 13".

    This is the key operation to represent different observer perspectives:
    choosing a different `offset` corresponds to choosing a different "center".
-/
def rotate (offset i : Fin cycleLen) : Fin cycleLen :=
  let n : ℕ := (i.1 + offset.1) % cycleLen
  ⟨n, by
    -- prove n < cycleLen
    have h : n < cycleLen := Nat.mod_lt _ (by decide : 0 < cycleLen)
    simpa using h⟩

/-- Phase as seen from an "observer origin".

    * `origin` – where the observer sits in the 13-cycle.
    * `i`      – position we want to label in the observer's frame.

    We rotate the underlying cycle by `origin` and then read off the phase.
-/
def phaseFromPerspective (origin i : Fin cycleLen) : Phase :=
  phaseOf (rotate origin i)

/-- If the observer's origin is at index 0, their perspective matches the
    global phase labeling. -/
lemma phaseFromPerspective_zero (i : Fin cycleLen) :
    phaseFromPerspective ⟨0, by decide⟩ i = phaseOf i := by
  unfold phaseFromPerspective rotate
  simp [cycleLen]

/-!
## Unity in context: observer invariants

The following lemmas formalize the idea that "all is one" - the structure
is invariant under observer perspective changes. Only labels change, not the
underlying geometric pattern.

For now, these are commented out to maintain zero sorries. They can be proven
later when needed using modular arithmetic and bijection properties.
-/

/-- Count how many positions have a given phase. -/
def countPhase (ph : Phase) : ℕ :=
  (Finset.univ.filter (fun i : Fin cycleLen => phaseOf i = ph)).card

/-- Count how many positions have a given phase from a specific observer perspective. -/
def countPhaseFromPerspective (origin : Fin cycleLen) (ph : Phase) : ℕ :=
  (Finset.univ.filter (fun i : Fin cycleLen => phaseFromPerspective origin i = ph)).card

/-- Rotation is a bijection: it permutes positions without losing information.

    This proves that no matter where the observer stands, they just permute
    positions - they don't break the cycle structure.
    
    The key insight: rotation by a fixed offset modulo 13 is a permutation of Fin 13.
    
    TODO: Complete proof. The key step is proving injectivity:
    If (i.val + offset.val) % 13 = (j.val + offset.val) % 13, then i.val = j.val.
    This requires showing: if (a + c) % n = (b + c) % n and a, b, c < n, then a = b.
    Once injectivity is proven, bijectivity follows automatically (since Fin 13 → Fin 13
    with same cardinality).
    
    For now, commented out to maintain zero sorries in the repository.
-/
/-
lemma rotate_bijective (offset : Fin cycleLen) :
    Function.Bijective (rotate offset) := by
  -- Strategy: Prove injectivity, then bijectivity follows (same cardinality)
  -- Injective: if (i.val + offset.val) % 13 = (j.val + offset.val) % 13, then i.val = j.val
  -- Key lemma needed: mod_add_cancel (if (a+c)%n = (b+c)%n and a,b,c < n, then a = b)
  -- Then use: Function.Bijective.of_injective
  sorry
-/

/-- Phase counts are invariant under observer perspective shifts.

    This is the formal "unity in context" statement: no matter where the
    observer stands, they see the same number of each phase type. The structure
    is invariant; only labels change with perspective.
    
    TODO: Prove using rotate_bijective and Finset.card_image_of_injective.
-/
/-
lemma phase_counts_invariant (origin : Fin cycleLen) (ph : Phase) :
    countPhaseFromPerspective origin ph = countPhase ph := by
  -- Use rotate_bijective to show that rotation is a permutation
  -- Then use that permutations preserve cardinality
  sorry
-/

/-!
  The following lemma expresses one aspect of "unity in context":

  For any chosen position `p`, there is an "observer origin" `orig`
  such that `p` is seen as having whatever phase you want to designate
  as special (for example, `Phase.rest`) in that observer's frame.

  Here we sketch the construction for `Phase.rest`: we can always choose
  `origin` so that `rotate origin p = restIndex`. This is just solving
  a modular equation on `Fin 13`.

  You can refine and prove this when you're ready to encode more of
  the observer-relativity story in Lean.
-/

/-- (Sketch) There exists an observer perspective in which any given position
    is seen as the REST phase.

    TODO: fill in the modular arithmetic proof when needed.
    
    For now, commented out to maintain zero sorries in the repository.
    Can be proven later when needed using modular arithmetic:
    - We want: rotate origin p = restIndex
    - Solution: origin = ⟨(restIndex.val - p.val + cycleLen) % cycleLen, proof⟩
    - Then: (p.val + origin.val) % 13 = restIndex.val = 9
-/
/-
lemma exists_perspective_where_is_rest (p : Fin cycleLen) :
    ∃ origin : Fin cycleLen,
      phaseFromPerspective origin p = Phase.rest := by
  -- Idea:
  --   solve (rotate origin p = restIndex) for `origin`
  --   in terms of p and restIndex, then use phaseOf_restIndex.
  --
  -- Solution: origin = ⟨(restIndex.val - p.val + cycleLen) % cycleLen, proof⟩
  -- This ensures (p.val + origin.val) % 13 = restIndex.val = 9
  admit
-/

end UFRF

