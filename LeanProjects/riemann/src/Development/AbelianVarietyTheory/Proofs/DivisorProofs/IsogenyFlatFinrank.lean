import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isogeny_flat_finrank : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  intro K _ A B f hf
  obtain ⟨hfin, hsurj⟩ := hf
  have hd := GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A B f
  have hdim : A.dim = B.dim := le_antisymm (hd.1 hfin) (hd.2 hsurj)
  have hflat : Flat f.hom.left := by
    have hAg := A.smooth
    have hBg : SmoothOfRelativeDimension A.dim B.X.hom := hdim ▸ B.smooth
    have h := GlobalTheory.IsogenyQuasiInverse.flat_fibre A.X B.X A.dim A.ab B.ab hAg hBg f.hom K (𝟙 _)
    have e' : f.hom.left = ((Over.pullbackId (X := Sp K)).inv.app A.X).left ≫
        ((Over.pullback (𝟙 (Sp K))).map f.hom).left ≫
          ((Over.pullbackId (X := Sp K)).hom.app B.X).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simp
    have i1 : IsIso ((Over.pullbackId (X := Sp K)).inv.app A.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).inv.app A.X)
    have i2 : IsIso ((Over.pullbackId (X := Sp K)).hom.app B.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).hom.app B.X)
    rw [e']
    exact Flat.comp _ _
  obtain ⟨hBint, hBnoeth, -⟩ := GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B
  have hdeg : deg f = f.hom.left.finrank B.origin := if_pos ⟨hfin, hsurj⟩
  have hconst : ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
    intro y
    rw [hdeg]
    exact (Scheme.Hom.isLocallyConstant_finrank f.hom.left).apply_eq_of_preconnectedSpace y B.origin
  refine ⟨hdim, hflat, ?_, hconst⟩
  have h1 := (Scheme.Hom.one_le_finrank_iff_surjective f.hom.left).mpr hsurj B.origin
  rw [hdeg]
  exact h1

end GlobalTheory.AV.AbVar
