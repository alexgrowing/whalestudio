import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsQuadraticExtension
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → admitted F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = y / σ y := by
  first | exact @GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm | exact GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm | (intros; apply GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm <;> assumption)
