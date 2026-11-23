import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 | exact GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 | (intros; apply GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 <;> assumption)
