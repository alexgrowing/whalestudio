import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_integral_multilinear_expansion : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X) (c : Fin e → σ → ℝ) (g : X → ℝ), IsNull A Uᶜ → (∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x) → (∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) → MIntegrable A (fun i => sumPot (c i) P) g ∧ mInt A (fun i => sumPot (c i) P) g = ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand | exact GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand <;> assumption)
