import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleRestrictedProductHaar
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
theorem _root_.GlobalTheory.T.idele_restricted_product_haar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μI : Measure (idelesAt E (evI F))), μI.IsHaarMeasure →
    ∀ (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μv v)) →
    ∀ (ν : Measure (AE F E)ˣ), GlobalTheory.RestrMeas.IsCylProd (W := Unit) (V := Pl F)
        (fun _ l => (⟨unitArch F E l, unitArch_mem l⟩ : idelesAt E (evI F)))
        (fun v l => (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v)))
        (fun v => {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v}) (fun _ => μI) μv ν →
    ∀ (T : Finset (Pl F)) (h : (AE F E)ˣ → ℂ) (q g : Pl F → (AE F E)ˣ → ℂ),
      Integrable (fun l : idelesAt E (evI F) => h l.1) μI →
      (∀ v ∈ T, Integrable (fun l : idelesAt E (evFin F v) => q v l.1) (μv v)) →
      (∀ᶠ v in cofinite, ∀ l ∈ unitsAt E v, g v l = 1) →
      (∀ v ∉ T, Integrable (fun l : idelesAt E (evFin F v) => g v l.1) (μv v)) →
      Summable (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1), ‖g v.1 l.1‖ ∂(μv v.1) - 1) →
      Integrable (fun l => h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) *
          ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l)) ν ∧
      ∫ l, h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂ν =
        (∫ l : idelesAt E (evI F), h l.1 ∂μI) * (∏ v ∈ T, ∫ l : idelesAt E (evFin F v), q v l.1 ∂(μv v)) *
          ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1) := by
  first | exact @GlobalTheory.ThK.ConeEuler.integral_euler_ideles | exact GlobalTheory.ThK.ConeEuler.integral_euler_ideles | (intros; apply GlobalTheory.ThK.ConeEuler.integral_euler_ideles <;> assumption)
