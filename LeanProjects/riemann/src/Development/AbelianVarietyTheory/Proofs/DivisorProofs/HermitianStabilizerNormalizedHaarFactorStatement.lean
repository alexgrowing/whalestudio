import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianStabilizerNormalizedHaarFactor
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
theorem _root_.GlobalTheory.T.hermitian_stabilizer_normalized_haar_factor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n r s : ℕ} {X : Spc F E n}, B.IsGood σ → X.IsHerm σ B r s →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKI : Measure (KAt K (evI F))) (μI : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKI → μI.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))),
    (∀ v, IsNormK K (evFin F v) (μKv v)) → (∀ v, IsNormE E v (μv v)) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T : Finset (Pl F)) (H : UA σ X.J → (AE F E)ˣ → ℂ) (Q : Pl F → UA σ X.J → (AE F E)ˣ → ℂ)
      (g : Pl F → (AE F E)ˣ → ℂ),
      Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) => H p.1.1 p.2.1) (μKI.prod μI) →
      (∀ k ∈ KAt K (evI F), Integrable (fun l : idelesAt E (evI F) => H k l.1) μI) →
      (∀ v ∈ T, Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) => Q v p.1.1 p.2.1) ((μKv v).prod (μv v))) →
      (∀ v ∈ T, ∀ k ∈ KAt K (evFin F v), Integrable (fun l : idelesAt E (evFin F v) => Q v k l.1) (μv v)) →
      (∀ v ∉ T, ∀ l l' : (AE F E)ˣ, l ∈ idelesAt E (evFin F v) → l⁻¹ * l' ∈ unitsAt E v → g v l' = g v l) →
      (∀ᶠ v in cofinite, ∀ l ∈ unitsAt E v, g v l = 1) →
      (∀ v ∉ T, Integrable (fun l : idelesAt E (evFin F v) => g v l.1) (μv v)) →
      Summable (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1), ‖g v.1 l.1‖ ∂(μv v.1) - 1) →
      (∀ k : K, Integrable (fun l => H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l)) μ) ∧
      Integrable (fun k : K => ∫ l, H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ) μK ∧
      ∫ k : K, ∫ l, H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ ∂μK =
        κ * (∫ k : KAt K (evI F), ∫ l : idelesAt E (evI F), H k.1 l.1 ∂μI ∂μKI) *
          (∏ v ∈ T, ∫ k : KAt K (evFin F v), ∫ l : idelesAt E (evFin F v), Q v k.1 l.1 ∂(μv v) ∂(μKv v)) *
          ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1) := by
  first | exact @GlobalTheory.ConeMeas.integral_comp_euler | exact GlobalTheory.ConeMeas.integral_comp_euler | (intros; apply GlobalTheory.ConeMeas.integral_comp_euler <;> assumption)
