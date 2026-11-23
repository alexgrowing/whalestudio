import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChart
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
theorem _root_.GlobalTheory.T.exists_form_nonvanishing_on_chart : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open <;> assumption)
