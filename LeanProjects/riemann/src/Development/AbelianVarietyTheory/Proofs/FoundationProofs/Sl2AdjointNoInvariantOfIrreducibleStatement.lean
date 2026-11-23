import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ v : Fin 3 → K, (∀ g, ad (ρ g) *ᵥ v = v) → v = 0 := by
  first | exact @GlobalTheory.ad_invariant_eq_zero_of_isIrr | exact GlobalTheory.ad_invariant_eq_zero_of_isIrr | (intros; apply GlobalTheory.ad_invariant_eq_zero_of_isIrr <;> assumption)
