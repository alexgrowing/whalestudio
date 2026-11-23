import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedSettingSymmetricCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.symmetric_charts_of_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w) (κ : Equiv.Perm (Fin S'.B.N)), S'.IsTied → SymmCharts M S'.B.toPotentialCharts κ → (∀ v, S'.ρ.toFun (star v) = S'.ρ.toFun v) → (∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), S'.η (κ j) (M.proj (conjVec z)) = S'.η j (M.proj z)) → IsConjInvariantH S'.ref → (∀ z ∈ mcPts (mCoordIdeal D.y), S'.B.ph (M.proj (conjVec z)) = S'.B.ph (M.proj z)) → ConjU S' := by
  first | exact @LevelTowerAlt.tied_setting_symmetric_charts | exact LevelTowerAlt.tied_setting_symmetric_charts
