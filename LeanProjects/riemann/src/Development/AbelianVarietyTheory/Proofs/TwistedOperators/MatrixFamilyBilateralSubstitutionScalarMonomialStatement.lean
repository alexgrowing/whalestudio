import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial : ∀ {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ), GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  first | exact @GlobalTheory.CompactHowe.substF_scalar_monomial | exact GlobalTheory.CompactHowe.substF_scalar_monomial | (intros; apply GlobalTheory.CompactHowe.substF_scalar_monomial <;> assumption)
