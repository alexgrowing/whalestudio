import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentLocalUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_different_local_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧
    ∃ s : 𝓞 F, s ∉ v.asIdeal ∧
    (∀ t : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) → IsIntegral ℤ (δ * t)) ∧
    (∀ t : E, IsIntegral ℤ (δ * t) → ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (algebraMap F E (s : F) * t)))) := by
  first | exact @GlobalTheory.ImagDifferent.exists_imag_generator | exact GlobalTheory.ImagDifferent.exists_imag_generator | (intros; apply GlobalTheory.ImagDifferent.exists_imag_generator <;> assumption)
