import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_pencilLineDiscriminant_le : ∀ (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ ξ₀ ξ₁ : Fin N → F, (GlobalTheory.PencilDisc.disc δ (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => MvPolynomial.C (ξ₀ j)) (fun j => MvPolynomial.C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  first | exact @GlobalTheory.PencilDiscDeg.totalDegree_disc_le | exact GlobalTheory.PencilDiscDeg.totalDegree_disc_le | (intros; apply GlobalTheory.PencilDiscDeg.totalDegree_disc_le <;> assumption)
