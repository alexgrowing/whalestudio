import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAdelesSubring
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_adeles_subring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type), ∃ R : Subring (ι → AE F E), (R : Set (ι → AE F E)) = Bdd F E ι := by
  first | exact @GlobalTheory.BddAdeleRing.exists_subring_eq_bdd | exact GlobalTheory.BddAdeleRing.exists_subring_eq_bdd | (intros; apply GlobalTheory.BddAdeleRing.exists_subring_eq_bdd <;> assumption)
