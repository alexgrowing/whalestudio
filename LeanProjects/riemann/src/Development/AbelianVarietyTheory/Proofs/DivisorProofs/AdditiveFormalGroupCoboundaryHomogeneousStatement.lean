import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_formal_group_coboundary_homogeneous : ∀ (R : Type) [CommRing R] (d N : ℕ), (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ (cob1 (addLaw R d) f) = 0) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≠ N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≠ N → coeff γ (cob2 (addLaw R d) c) = 0) ∧ (∀ (c : MvPowerSeries (Fin d ⊕ Fin d) R) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (swap c) = coeff (γ.mapDomain Sum.swap) c) ∧ ∀ (f : MvPowerSeries (Fin d) R) (β : Fin d →₀ ℕ) (i : Fin d), β ≠ 0 → coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (cob1 (addLaw R d) f) = ((β i + 1 : ℕ) : R) * coeff (β + Finsupp.single i 1) f := by
  first | exact @GlobalTheory.homog_cob_addLaw | exact GlobalTheory.homog_cob_addLaw | (intros; apply GlobalTheory.homog_cob_addLaw <;> assumption)
