import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramDetEqNormSqBasisDetMul
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFam_gram_det_eq_normSq_basis_det_mul : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) (σ : F →+* ℂ) (d : ℕ) (b : Module.Basis (Fin d) F V) (v : Fin d → V), (nm.gram σ v).det = ((Complex.normSq (σ (b.det v)) : ℝ) : ℂ) * (nm.gram σ ⇑b).det := by
  first | exact @GlobalTheory.GramChange.gram_det | exact GlobalTheory.GramChange.gram_det | (intros; apply GlobalTheory.GramChange.gram_det <;> assumption)
