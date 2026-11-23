import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedKummerOfCoprimeUnit
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  first | exact @GlobalTheory.CNorm.kummer_valuation_unramified | exact GlobalTheory.CNorm.kummer_valuation_unramified | (intros; apply GlobalTheory.CNorm.kummer_valuation_unramified <;> assumption)
