import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeDimZeroFibreDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteCoverRelDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteCoverRefineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeRankGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBoundStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.Vert.Model.Hom

theorem exists_finite_free_off_codim_two : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∃ (U : B.X.Opens) (n : ℕ), 0 < n ∧ f.fibreDeg 1 = n ∧ topologicalKrullDim ((U : Set B.X)ᶜ : Set B.X) + 1 ≤ (B.relDim : WithBot ℕ∞) ∧ ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧ (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n) := by
  intro O _ _ _ B B' f hN h0
  obtain ⟨hpos, hdeg⟩ := GlobalTheory.T.relative_dim_zero_fibre_degree O B B' f h0
  let n := Module.finrank f.fnField Γ(f.genFibre, ⊤)
  let P : B.X.Opens → Prop := fun V => IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
    (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧
      Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n)
  let U : B.X.Opens := ⨆ V : {V : B.X.Opens // P V}, V.1
  refine ⟨U, n, hpos, hdeg, ?_, fun x hx => ?_⟩
  · refine GlobalTheory.T.closed_complement_dim_bound B.X U B.relDim B.dim_eq fun y hy => ?_
    obtain ⟨V, hyV, hV, hV', hfin⟩ := GlobalTheory.T.affine_finite_cover_rel_dim_zero O B B' f h0 y hy
    obtain ⟨W, hyW, hW, hW', hfree, hfin'⟩ := GlobalTheory.T.affine_finite_cover_refine O B B' f hN y hy V hyV hV hV' hfin
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hW', hfree, hfin',
      GlobalTheory.T.finite_free_rank_generic_fibre O B B' f W ⟨y, hyW⟩ hW hW' hfree hfin'⟩, hyW⟩
  · obtain ⟨⟨V, hP⟩, hxV⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨V, hxV, le_iSup (fun V : {V : B.X.Opens // P V} => V.1) ⟨V, hP⟩, hP⟩

end GlobalTheory.Vert.Model.Hom
