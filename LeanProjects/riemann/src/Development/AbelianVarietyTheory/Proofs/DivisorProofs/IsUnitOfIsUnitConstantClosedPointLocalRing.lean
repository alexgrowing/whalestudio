import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.unit_of_isUnit_cst_closedPoint : ∀ (V : Type) [CommRing V] [IsLocalRing V] (a : V), IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a) → IsUnit a := by
  intro V _ _ a h
  have e := gs_eq (𝟙 (Sp V)) (closedPoint V) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have h' : IsUnit ((Sp V).presheaf.germ ⊤ (closedPoint V) trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := by
    have h2 : IsUnit (gs (𝟙 (Sp V)) (closedPoint V) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := h
    rw [e] at h2
    simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact h2
  have hm := (Scheme.mem_basicOpen_top (X := Sp V) ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) (closedPoint V)).mpr h'
  rw [basicOpen_eq_of_affine] at hm
  by_contra ha
  exact ((PrimeSpectrum.mem_basicOpen _ _).mp hm) ((IsLocalRing.mem_maximalIdeal a).mpr ha)
