import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_points_siegel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q' : Set (GA E N)) (ω : Set (GA E N)) (t₀ : ℝ)
  (Q : Set (GA E N)), IsCompact Q' → IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := N) : Set _) → IsCompact Q → ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin N → ℝ,
    (∀ r, -t₀ ≤ An.sr x r) → ∀ q ∈ Q,
    {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ Q', ∃ a' ∈ Q', γ = (b * An.tor E x * q) * a * a'⁻¹ * (b * An.tor E x * q)⁻¹}.encard ≤
      (⌈C * Real.exp (M * ∑ r ∈ Finset.range N, An.sr x r)⌉₊ : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | exact GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | (intros; apply GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel <;> assumption)
