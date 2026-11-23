import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StrictWeightGrowthBound
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
theorem _root_.GlobalTheory.T.strict_weight_growth_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∃ (C : ℝ) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (RootIx Dw) → ℤ) (θ : ℕ → (T.M B b).Ω), 0 ≤ C ∧ (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧ (∀ n, 0 < q n ∧ 8 ∣ q n ∧ θ n ≠ 0) ∧ (∀ n j, (m n j : ℝ) = q n * (T.M B b).coef (T.lamS (reW u) (s n)) (s n) j) ∧ ∀ (n τ : ℕ) (t : ℝ), ∀ σ ∈ chartLatNm (T.M B b).y (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)).a τ, IsSmallH (mCoordIdeal (T.M B b).y) (T.M B b).y (Small.shiftH (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)) (q n * t)) τ σ → σ * θ n ^ τ ∈ modelSmall (o.toTowerOrigin.Or B b) ((τ * q n) • u) (Real.exp (((τ * q n : ℕ) : ℝ) * (t + C * s n))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.Mult.vs_mult | exact GlobalTheory.CompanionTheory.Ar.Plug.Mult.vs_mult | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.Mult.vs_mult <;> assumption)
