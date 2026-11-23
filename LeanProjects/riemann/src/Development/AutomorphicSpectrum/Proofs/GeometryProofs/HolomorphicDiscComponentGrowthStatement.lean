import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscComponentGrowth
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_component_growth : (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖) → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (Hb : ((Σ k, ι k) → ℂ) → ℝ) (w f₀ : MRing ι), Birational y → SmoothGenericFibreM y → Small.IsFormOff (mCoordIdeal y) w → Small.IsFormOff (mCoordIdeal y) f₀ → (∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z w ≠ 0 → Small.ValLe y a s z (Hb z)) → (∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → MvPolynomial.aeval (Zf z) f₀ ≠ 0) → ∃ (C ρ : ℝ) (M : ℕ), 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Hb (Zf z) ≤ C * (1 + |Real.log ‖z‖|) ^ M) → ∃ N : ℕ, 0 < N ∧ (N : Ω) * s ∈ chartLatNm y a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc | exact GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc <;> assumption)
