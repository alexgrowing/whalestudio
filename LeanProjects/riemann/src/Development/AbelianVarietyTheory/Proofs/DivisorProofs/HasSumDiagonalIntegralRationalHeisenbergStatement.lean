import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDiagonalIntegralRationalHeisenberg
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_diagonalIntegral_rationalHeisenberg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F (κ ⊕ κ), HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) (c * thetaSum F φ) := by
  first | exact @GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat | exact GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat | (intros; apply GlobalTheory.ThetaRatSum.hasSum_lDiag_schr_rat <;> assumption)
