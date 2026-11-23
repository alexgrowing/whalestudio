import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HadamardIneqComplexCombinationsBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hadamard_ineq_complex_combinations_basis : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) (d : ℕ) (b : Module.Basis (Fin d) F V) (σ : F →+* ℂ) (P : Matrix (Fin d) (Fin d) ℂ), 0 < (nm.gram σ b).det.re ∧ ‖P.det‖ * Real.sqrt (nm.gram σ b).det.re ≤ ∏ k, cnrm nm σ (fun i => P i k) b := by
  first | exact @GlobalTheory.HSShort.hadamard_basis_comb | exact GlobalTheory.HSShort.hadamard_basis_comb | (intros; apply GlobalTheory.HSShort.hadamard_basis_comb <;> assumption)
