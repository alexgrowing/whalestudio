import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaForms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_functional_vanishes_on_omega_forms : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I → ∀ y ∈ omA k x I, ρ y = 0 := by
  first | (exact @GlobalTheory.PD.ResVan.resvan) | (exact GlobalTheory.PD.ResVan.resvan) | (intros; apply GlobalTheory.PD.ResVan.resvan <;> assumption)
