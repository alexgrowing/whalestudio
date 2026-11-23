import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_blockSymbolMatrix_ne_zero' : ∀ (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J] (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E), (∀ p, g p ≠ 0) → R.det ≠ 0 → (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  first | exact @GlobalTheory.det_blockSymbolMatrix_ne_zero | exact GlobalTheory.det_blockSymbolMatrix_ne_zero | (intros; apply GlobalTheory.det_blockSymbolMatrix_ne_zero <;> assumption)
