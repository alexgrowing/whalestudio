import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerNormalizedHaarRestricted
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_normalized_haar_restricted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n r s : ℕ} {X : Spc F E n}, B.IsGood σ → X.IsHerm σ B r s →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (μK : Measure K), μK.IsHaarMeasure →
    ∀ (μKI : Measure (KAt K (evI F))), IsNormK K (evI F) μKI →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∃ κK : ℝ, 0 < κK ∧ ∀ (T : Finset (Pl F)) (a : UA σ X.J → ℂ) (b : Pl F → UA σ X.J → ℂ),
      Integrable (fun k : KAt K (evI F) => a k.1) μKI →
      (∀ v ∈ T, Integrable (fun k : KAt K (evFin F v) => b v k.1) (μKv v)) →
      Integrable (fun k : K => a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1)) μK ∧
      ∫ k : K, a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1) ∂μK =
        κK * (∫ k : KAt K (evI F), a k.1 ∂μKI) * ∏ v ∈ T, ∫ k : KAt K (evFin F v), b v k.1 ∂(μKv v) := by
  first | exact @GlobalTheory.ThK.ConeEuler.CompIntegral.integral_components | exact GlobalTheory.ThK.ConeEuler.CompIntegral.integral_components | (intros; apply GlobalTheory.ThK.ConeEuler.CompIntegral.integral_components <;> assumption)
