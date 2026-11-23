import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.finite_stalk_quot_integral : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  intro X Y p hp y a
  obtain ⟨U, hU', hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p y) trivial
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU'.preimage p
  have hyV : y ∈ p ⁻¹ᵁ U := hyU
  letI : Algebra Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  haveI := hV.isLocalization_stalk ⟨y, hyV⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.mk'_surjective (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl a
  have hfin : (p.app U).hom.Finite := p.finite_app U hU'
  have hint := hfin.to_isIntegral
  have key : ∀ z : Γ(Y, p ⁻¹ᵁ U), ∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧
      P.eval₂ (p.stalkMap y).hom (algebraMap Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) z) = 0 := by
    intro z
    obtain ⟨P', hm, hP'⟩ := hint z
    refine ⟨P'.map (X.presheaf.germ U (p y) hyU).hom, hm.map _, ?_⟩
    have hc : (p.stalkMap y).hom.comp (X.presheaf.germ U (p y) hyU).hom
        = (Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom.comp (p.app U).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap]
    rw [Polynomial.eval₂_map, hc]
    change Polynomial.eval₂ _ ((Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom z) P' = 0
    rw [← Polynomial.hom_eval₂, hP', map_zero]
  refine ⟨algebraMap _ _ c, algebraMap _ _ (t : Γ(Y, p ⁻¹ᵁ U)), IsLocalization.map_units _ t, ?_, key c, key t⟩
  rw [← hct]
  exact IsLocalization.mk'_spec _ c t
