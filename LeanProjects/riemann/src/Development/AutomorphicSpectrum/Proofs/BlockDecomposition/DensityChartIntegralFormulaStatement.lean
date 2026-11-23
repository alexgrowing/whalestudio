import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_chart_integral_formula : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces <;> assumption)
