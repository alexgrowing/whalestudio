import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma length_self_eq {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  have h : ((Module.length R R : ℕ∞) : WithBot ℕ∞) = (Module.length R' R' : ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm
  exact_mod_cast h

private lemma length_stalk_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (hy : f x = y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  subst hy
  exact length_self_eq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.multBC_of :
    MultBC := by
  intro Z' S' Z S v p' p g h
  funext Ω _ _ z
  have hw : (z ≫ p') ≫ g = (z ≫ v) ≫ p := by
    simp only [Category.assoc, h.w]
  have hP : IsPullback (pullback.fst p' (z ≫ p') ≫ v) (pullback.snd p' (z ≫ p')) p ((z ≫ v) ≫ p) := by
    rw [← hw]
    exact (IsPullback.of_hasPullback p' (z ≫ p')).paste_horiz h
  have hl : (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p')) ≫ hP.isoPullback.hom =
      pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  have hpt : hP.isoPullback.hom (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p'))) =
      pt (pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p ((z ≫ v) ≫ p)) := by
    rw [← pt_comp, hl]
  simp only [Wt.comap, mult]
  rw [length_stalk_eq hP.isoPullback.hom _ _ hpt]
