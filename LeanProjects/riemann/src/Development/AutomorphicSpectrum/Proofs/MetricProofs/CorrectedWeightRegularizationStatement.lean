import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  first | exact @GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | exact GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | (intros; apply GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization <;> assumption)
