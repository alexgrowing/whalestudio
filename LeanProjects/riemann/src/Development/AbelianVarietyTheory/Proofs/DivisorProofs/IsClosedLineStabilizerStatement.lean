import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLineStabilizer
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
theorem _root_.GlobalTheory.T.isClosed_line_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (x : Fin n → E), x ≠ 0 →
    IsClosed (lineStab σ X x : Set (UAtSub σ X (evI F))) := by
  first | exact @GlobalTheory.IwasawaKAvgInt.isClosed_lineStab_arch | exact GlobalTheory.IwasawaKAvgInt.isClosed_lineStab_arch | (intros; apply GlobalTheory.IwasawaKAvgInt.isClosed_lineStab_arch <;> assumption)
