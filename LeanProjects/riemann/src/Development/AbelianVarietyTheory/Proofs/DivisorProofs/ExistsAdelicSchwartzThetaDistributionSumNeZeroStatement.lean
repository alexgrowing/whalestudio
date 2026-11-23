import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  first | exact @GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | exact GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | (intros; apply GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero <;> assumption)
