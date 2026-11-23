import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstMemBoundedAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_mem_bounded_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type) (e : E), (fun _ : ι => inclR (F := F) (AF F) e) ∈ Bdd F E ι := by
  first | exact @GlobalTheory.ConstBdd.const_mem_Bdd | exact GlobalTheory.ConstBdd.const_mem_Bdd | (intros; apply GlobalTheory.ConstBdd.const_mem_Bdd <;> assumption)
