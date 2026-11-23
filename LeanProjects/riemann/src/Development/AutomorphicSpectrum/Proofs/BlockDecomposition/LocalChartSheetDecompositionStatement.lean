import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecomposition
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
theorem _root_.GlobalTheory.T.local_chart_sheet_decomposition : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density <;> assumption)
