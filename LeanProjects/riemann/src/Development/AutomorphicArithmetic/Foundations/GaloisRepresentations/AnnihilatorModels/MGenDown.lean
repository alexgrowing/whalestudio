import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma closed_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O)) (z : X) :
    s z = IsLocalRing.closedPoint O ↔ z ∉ X.basicOpen (fn s ϖ) := by
  have key : z ∈ X.basicOpen (fn s ϖ) ↔ ϖ ∉ (s z).asIdeal := by
    rw [show X.basicOpen (fn s ϖ) = s ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) from (Scheme.preimage_basicOpen_top s _).symm]
    change s z ∈ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) ↔ _
    rw [basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [key, not_not]
  constructor
  · intro h
    have hm : (s z).asIdeal = IsLocalRing.maximalIdeal O := congrArg PrimeSpectrum.asIdeal h
    rw [hm]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · intro h
    have hne : (s z).asIdeal ≠ ⊥ := fun hb0 => hϖ.ne_zero (by simpa [hb0] using h)
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (s z).2))

theorem UpperTheory.Gal.crystallineComparison.Mod.genDown_of :
    GenDown := by
  intro O _ _ _ ϖ hϖ X Y s h hflat y hy
  have hc : ∀ y' : Y, s (h y') = IsLocalRing.closedPoint O ↔
      y' ∉ Y.basicOpen (fn (h ≫ s) ϖ) := by
    intro y'
    rw [← closed_iff hϖ (h ≫ s) y', Scheme.Hom.comp_apply]
  refine ⟨(hc y).mpr hy.1, fun z' hz' hsp => ?_⟩
  obtain ⟨y', hy'sp, rfl⟩ := Flat.generalizingMap h hsp
  have := hy.2 y' ((hc y').mp hz') hy'sp
  rw [this]
