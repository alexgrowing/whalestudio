import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerNormalizedLocalProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_stabilizer_normalized_local_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (K : Subgroup (UA σ X.J)), IsStab B K → ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    SigmaFinite μK ∧ SigmaFinite μ ∧ SigmaFinite (μKi.map Subtype.val) ∧ SigmaFinite (μEi.map Subtype.val) ∧
    (∀ v, SigmaFinite ((μKv v).map Subtype.val) ∧ SigmaFinite ((μEv v).map Subtype.val)) ∧
    (∀ v, Measurable fun p : K × (AE F E)ˣ => (compAt σ X.J v p.1.1, unitAt E v p.2)) ∧
    Measurable (fun p : K × (AE F E)ˣ => (compArch σ X.J p.1.1, unitArch F E p.2)) ∧
    (∀ v, MeasurableSet {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v}) ∧
    (∀ v, ((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)
      {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v} = 1) ∧
    (∀ p : K × (AE F E)ˣ, ∀ᶠ v in cofinite, compAt σ X.J v p.1.1 ∈ KAt K (evFin F v) ∧ unitAt E v p.2 ∈ unitsAt E v) ∧
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ GlobalTheory.RestrMeas.IsCylProd (W := Unit) (V := Pl F)
      (fun _ (p : K × (AE F E)ˣ) => (compArch σ X.J p.1.1, unitArch F E p.2))
      (fun v p => (compAt σ X.J v p.1.1, unitAt E v p.2))
      (fun v => {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v})
      (fun _ => (μKi.map Subtype.val).prod (μEi.map Subtype.val))
      (fun v => ((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val))
      (κ • μK.prod μ) := by
  first | exact @GlobalTheory.ThK.EulerMeas.haar_isCylProd | exact GlobalTheory.ThK.EulerMeas.haar_isCylProd | (intros; apply GlobalTheory.ThK.EulerMeas.haar_isCylProd <;> assumption)
