import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsExponentPolynomialDiscrete
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_polynomial_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ), 0 < r → r < N → ∃ D : ℕ, ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
  (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m) → ∀ φ ∈ V, ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r φ.1 p ∧
    ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  first | exact @GlobalTheory.CompanionTheory.KillU.killU | exact GlobalTheory.CompanionTheory.KillU.killU | (intros; apply GlobalTheory.CompanionTheory.KillU.killU <;> assumption)
