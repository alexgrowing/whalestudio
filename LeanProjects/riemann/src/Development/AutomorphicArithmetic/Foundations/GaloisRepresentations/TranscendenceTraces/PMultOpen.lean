import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (f : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  haveI : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  haveI : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.symm _ _
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f.toSemilinearEquiv)

private theorem length_stalk_eq {X Y : Scheme.{0}} (e : X ⟶ Y) [IsOpenImmersion e] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (e x)) (Y.presheaf.stalk (e x)) := by
  exact (length_self_eq_of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multOpen_of :
    MultOpen := by
  intro W Z S j _ p
  funext Ω _ _ z
  have e1 : (j ≫ p) ≫ 𝟙 S = j ≫ p := by simp
  have e2 : (z ≫ j ≫ p) ≫ 𝟙 S = 𝟙 (gp Ω) ≫ (z ≫ j) ≫ p := by simp
  let m := pullback.map (j ≫ p) (z ≫ j ≫ p) p ((z ≫ j) ≫ p) j (𝟙 _) (𝟙 S) e1 e2
  have hm : IsOpenImmersion m := by infer_instance
  have hx : pullback.lift z (𝟙 (gp Ω)) (by simp) ≫ m =
      pullback.lift (z ≫ j) (𝟙 (gp Ω)) (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hl := length_stalk_eq m (pt (pullback.lift z (𝟙 (gp Ω)) (by simp)))
  rw [← pt_comp, hx] at hl
  simp only [mult, Wt.comap]
  rw [hl]
