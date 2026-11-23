import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ → IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  first | exact @GlobalTheory.FinPl.PutIn.isSBHalf_tens | exact GlobalTheory.FinPl.PutIn.isSBHalf_tens | (intros; apply GlobalTheory.FinPl.PutIn.isSBHalf_tens <;> assumption)
