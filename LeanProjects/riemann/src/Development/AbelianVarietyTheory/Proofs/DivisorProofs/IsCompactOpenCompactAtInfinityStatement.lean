import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOpenCompactAtInfinity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_open_compact_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → IsCompact (KAt K (evI F) : Set (UA σ X.J)) := by
  first | exact @GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf | exact GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf | (intros; apply GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf <;> assumption)
