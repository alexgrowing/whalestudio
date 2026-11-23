import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabSurjectiveOfStableRangeInduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabInjectiveOfStableRangeInducti
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem kStability_main : UpperTheory.V.Published.KStability := by
  intro R _ s hs
  have key : ∀ i : ℕ, ∀ m m' (h : m ≤ m'), m' = m + 1 →
      (2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom) ∧
      (2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have hyp : ∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 →
          (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧
          (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom) :=
        fun q m m' h hq hm => ih q hq m m' h hm
      intro m m' h hm
      exact ⟨GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction R s hs i hyp m m' h hm, GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction R s hs i hyp m m' h hm⟩
  intro i n hn
  have h1 := key i n (n + 1) (Nat.le_succ n) rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(h1.2 hn), (h1.1 (by omega))⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
end
