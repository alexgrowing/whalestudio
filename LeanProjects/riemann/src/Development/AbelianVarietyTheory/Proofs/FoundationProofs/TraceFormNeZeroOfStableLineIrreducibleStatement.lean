import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  first | exact @GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | exact GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | (intros; apply GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr <;> assumption)
