import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  first | exact @GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | exact GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | (intros; apply GlobalTheory.SchANonzero.exists_mem_schA_ne_zero <;> assumption)
