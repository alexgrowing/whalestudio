import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff : ∀ (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ (u : Fin D → Fin N → R) (a b : Fin N → R), (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧ (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  first | exact @GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | exact GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | (intros; apply GlobalTheory.PencilDisc.line_natDegree_le_and_coeff <;> assumption)
