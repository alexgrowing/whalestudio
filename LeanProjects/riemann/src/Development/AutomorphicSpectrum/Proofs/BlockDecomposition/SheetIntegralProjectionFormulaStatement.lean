import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIntegralProjectionFormula
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
theorem _root_.GlobalTheory.T.sheet_integral_projection_formula : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1) → IsGoodProj (ptIdeal (i (genericPoint X))) Ψ →
    ∀ {ι : Type} (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
      (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)),
      (∀ l, GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N (e l) (Γ l)) → (∀ l, S l ⊆ (e l).source) →
      Pairwise (Function.onFun Disjoint S) → ∀ v : Fin D → ℂ,
      (∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ y ∈ ⋃ l, S l) →
      ∀ (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ),
      (∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) →
      ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w = ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq <;> assumption)
