import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramified
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → ContainsAbove S l → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) → Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  first | exact @GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | exact GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | (intros; apply GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt <;> assumption)
