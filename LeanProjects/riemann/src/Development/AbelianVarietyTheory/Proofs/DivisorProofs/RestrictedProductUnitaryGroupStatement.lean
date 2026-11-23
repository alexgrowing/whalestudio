import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s' : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s' → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    GlobalTheory.RestrMeas.IsRestrGroup (X := UA σ X.J) (W := Unit) (V := Pl F)
      (fun _ => (compArch σ X.J).codRestrict (UAtSub σ X (evI F)) compArch_mem)
      (fun v => (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v))
      (fun v => K.subgroupOf (UAtSub σ X (evFin F v))) := by
  first | exact @GlobalTheory.UnitaryRestr.isRestrGroup_UA | exact GlobalTheory.UnitaryRestr.isRestrGroup_UA | (intros; apply GlobalTheory.UnitaryRestr.isRestrGroup_UA <;> assumption)
