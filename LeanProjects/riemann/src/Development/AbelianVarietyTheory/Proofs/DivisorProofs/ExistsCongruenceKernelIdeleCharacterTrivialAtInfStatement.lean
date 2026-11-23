import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity : ∀ (F : Type) [Field F] [NumberField F] (lam : (AF F)ˣ →* Circle), Continuous lam →
    (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) → ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  first | exact @GlobalTheory.HeckeExtend.exists_cong_ker | exact GlobalTheory.HeckeExtend.exists_cong_ker | (intros; apply GlobalTheory.HeckeExtend.exists_cong_ker <;> assumption)
