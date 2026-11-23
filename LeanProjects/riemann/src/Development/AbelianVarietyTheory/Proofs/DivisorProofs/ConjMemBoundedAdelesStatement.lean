import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBoundedAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_bounded_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ι : Type) (f : ι → AE F E), f ∈ Bdd F E ι → (fun t => cA σ (f t)) ∈ Bdd F E ι := by
  first | exact @GlobalTheory.CAConjBdd.cA_mem_Bdd | exact GlobalTheory.CAConjBdd.cA_mem_Bdd | (intros; apply GlobalTheory.CAConjBdd.cA_mem_Bdd <;> assumption)
