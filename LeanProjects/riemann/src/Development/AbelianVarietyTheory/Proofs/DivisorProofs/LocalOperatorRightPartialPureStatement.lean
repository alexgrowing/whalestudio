import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_right_partial_pure : ∀ {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁'] (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ), IsLocOp e → ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  first | exact @GlobalTheory.DblEval.BlockSwap.partR_pureA | exact GlobalTheory.DblEval.BlockSwap.partR_pureA | (intros; apply GlobalTheory.DblEval.BlockSwap.partR_pureA <;> assumption)
