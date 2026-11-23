import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownwardChartLocalHolomorphicSection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downward_chart_local_holomorphic_section : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (σ : 𝓞 F →+* ℂ) (c : AlgChart V.p σ e) (y : CxPts V.p σ), y ∈ c.e.source → ∀ (j : Fin (M.A (ε σ)).n), π σ y ∈ ((M.A (ε σ)).chart j).source → ∃ U : Set (ReciprocityTheory.L2DbarEstimates.V e), IsOpen U ∧ c.e y ∈ U ∧ U ⊆ c.e.target ∧ (∀ v ∈ U, π σ (c.e.symm v) ∈ ((M.A (ε σ)).chart j).source) ∧ DifferentiableOn ℂ (fun v => FinChart.toV e (((M.A (ε σ)).chart j) (π σ (c.e.symm v)))) U := by
  first | exact @GlobalTheory.Mean4O.Cover.differentiableOn_chart_of_isDown | exact GlobalTheory.Mean4O.Cover.differentiableOn_chart_of_isDown | (intros; apply GlobalTheory.Mean4O.Cover.differentiableOn_chart_of_isDown <;> assumption)
