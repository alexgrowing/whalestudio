import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAdelesModGlobalElements
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_adeles_mod_global_elements : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type) (z : ι → AE F E), ∃ e : ι → E, (fun t => z t - inclR (F := F) (AF F) (e t)) ∈ Bdd F E ι := by
  first | exact @GlobalTheory.QhtUnip.exists_rat_sub_mem_bdd | exact GlobalTheory.QhtUnip.exists_rat_sub_mem_bdd | (intros; apply GlobalTheory.QhtUnip.exists_rat_sub_mem_bdd <;> assumption)
