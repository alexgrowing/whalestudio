import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAbsGtOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_abs_gt_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  first | exact @GlobalTheory.DivAbsBig.exists_idele_absE_gt_one | exact GlobalTheory.DivAbsBig.exists_idele_absE_gt_one | (intros; apply GlobalTheory.DivAbsBig.exists_idele_absE_gt_one <;> assumption)
