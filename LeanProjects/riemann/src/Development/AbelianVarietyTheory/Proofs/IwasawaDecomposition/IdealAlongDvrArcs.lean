import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

open GlobalTheory.FlagMod

variable {X : Scheme.{0}}

theorem gs_spMap_eq {A F : Type} [CommRing A] [Field F] (φ : A →+* F) (y : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)) : gs (spMap φ ≫ y) z U a = toStk z (φ (ev y U h a)) := by
  have h' := le_preimage_comp (spMap φ) h
  have e : φ (ev y U h a) = ev (spMap φ ≫ y) U h' a := by rw [ev_spMap φ y U h h']; rfl
  rw [e, gs_eq _ z U (h' trivial)]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _))
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') z trivial _).symm

theorem exists_gen_const {L : LB X} (hL : L.IsLB) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : L.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) (c : Aˣ) : ∃ e : LB.Gen (L.pull y), e.IsGen ∧
      ∀ (F : Type) [Field F] (φ : A →+* F) (z : Sp F),
        (gm (spMap φ) z (LB.wchart L (fun _ : PUnit => y) fun _ => k) (e.s fun _ => k)).val = toStk z (φ c) := by
  obtain ⟨t, ht⟩ := DVR.exists_gen_of_local L hL (fun _ : PUnit => y) (fun _ => 1)
  have hle : ⊤ ≤ LB.wchart L (fun _ : PUnit => y) fun _ => k := fun p hp => Set.mem_iInter.2 fun _ => hk hp
  let C : Γ(Sp A, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom c
  refine ⟨Geo.Tor.scaleGen t (C * res hle (t.s fun _ => k)⁻¹), scaleGen_isGen hL t ht _, fun F _ φ z => ?_⟩
  have e := gm_scaleGen t (C * res hle (t.s fun _ => k)⁻¹) (spMap φ) z (fun _ => k) (hle trivial)
  have e' : gm (spMap φ) z ⊤ (C * res hle (t.s fun _ => k)⁻¹) = gm (spMap φ) z ⊤ C *
      (gm (spMap φ) z (LB.wchart L (fun _ : PUnit => y) fun _ => k) (t.s fun _ => k))⁻¹ :=
    (map_mul _ _ _).trans (congrArg _ ((gm_res _ z hle trivial _).trans (map_inv _ _)))
  refine (congrArg Units.val ((e.trans (congrArg (· * _) e')).trans (inv_mul_cancel_right _ _))).trans ?_
  rw [gm_val _ z ⊤ trivial]
  have e2 := congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  exact congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e2.symm

theorem pairing_eq (D : EffCartierData X) {Y Z : Scheme.{0}} {y : Y ⟶ X} {t : LB.Gen ((CechPic.dual D.lb).pull y)}
    (ht : t.IsGen) (r : Z ⟶ Y) (z : Z) {i j : D.ι} (hi : (r ≫ y) z ∈ D.U i) (hj : (r ≫ y) z ∈ D.U j) :
    (gm r z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => i) (t.s fun _ => i)).val *
        gs (r ≫ y) z (D.U i) (D.f i) =
      (gm r z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => j) (t.s fun _ => j)).val *
        gs (r ≫ y) z (D.U j) (D.f j) := by
  have hm : (r ≫ y) z ∈ D.U i ⊓ D.U j := ⟨hi, hj⟩
  have e₁ := gen_trans ht r z (j := fun _ => i) (j' := fun _ => j) (Set.mem_iInter.2 fun _ => hi)
    (Set.mem_iInter.2 fun _ => hj)
  have e₂ : trF (L := CechPic.dual D.lb) (fun _ : PUnit => y) (fun _ => 1) r z (fun _ => i) (fun _ => j) =
      (gm (r ≫ y) z (D.U i ⊓ D.U j) (D.trans i j))⁻¹ := by
    exact (Fintype.prod_unique _).trans ((zpow_one _).trans (map_inv _ _))
  have e₃ : gs (r ≫ y) z (D.U i) (D.f i) =
      (gm (r ≫ y) z (D.U i ⊓ D.U j) (D.trans i j)).val * gs (r ≫ y) z (D.U j) (D.f j) :=
    (gs_res _ z _ hm _).symm.trans ((congrArg (gs (r ≫ y) z _) (D.trans_spec i j)).trans ((gs_mul _ z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ z _ hm _) (gs_res _ z _ hm _))))
  rw [e₁, e₂, e₃, Units.val_mul, mul_comm (Units.val _⁻¹), _root_.mul_assoc, Units.inv_mul_cancel_left]

theorem exists_gen_pairing (D : EffCartierData X) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : D.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ D.U k) (c : Aˣ) : ∃ e : LB.Gen ((CechPic.dual D.lb).pull y), e.IsGen ∧
      ∀ (F : Type) [Field F] (φ : A →+* F) (z : Sp F) (i : D.ι), (spMap φ ≫ y) z ∈ D.U i →
        (gm (spMap φ) z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => i) (e.s fun _ => i)).val *
          gs (spMap φ ≫ y) z (D.U i) (D.f i) = toStk z (φ (c * ev y (D.U k) hk (D.f k))) := by
  obtain ⟨e, he, hc⟩ := exists_gen_const (CechPic.isLB_dual D.isLB_lb) y k hk c
  refine ⟨e, he, fun F _ φ z i hi => (pairing_eq D he (spMap φ) z hi (hk trivial)).trans ?_⟩
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) (hc F φ z) (gs_spMap_eq φ y _ hk z _)

theorem idlAlong_idealSheaf_eq (D : EffCartierData X) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : D.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ D.U k) : idlAlong D.idealSheaf y = Ideal.span {ev y (D.U k) hk (D.f k)} := by
  obtain ⟨W, hW, hle⟩ := EffCartierData.exists_affine_le (show y (closedPoint A) ∈ D.U k from hk trivial)
  have hW' : ⊤ ≤ y ⁻¹ᵁ W.1 := (Scheme.preimage_eq_top_of_closedPoint_mem y hW).ge
  rw [TraitOrder.idlAlong_eq_map _ y W hW', D.ideal_idealSheaf W k hle, Ideal.map_span, Set.image_singleton,
    ← ev_res y hle hW' hk]
  rfl

theorem exists_dual_gen_extAt : ∀ (X : Scheme.{0}) (BD : GlobalTheory.EffCartierData X) (R : Type) [CommRing R] [IsDomain R] (u : R), u ≠ 0 →
    ∀ (x : Sp (FractionRing R) ⟶ X) (n : ℕ),
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ u ^ n}) →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.dual BD.lb).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.dual BD.lb) x e := by
  intro X BD R _ _ u hu x n H
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing BD.cover x
  have hu' : algebraMap R (FractionRing R) u ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hu)
  obtain ⟨c, hc⟩ : ∃ c : (FractionRing R)ˣ, ev x (BD.U k) hk (BD.f k) ≠ 0 →
      c * ev x (BD.U k) hk (BD.f k) = algebraMap R (FractionRing R) u ^ n := by
    by_cases ha : ev x (BD.U k) hk (BD.f k) = 0
    · exact ⟨1, fun h => (h ha).elim⟩
    · exact ⟨Units.mk0 _ (div_ne_zero hu' ha), fun _ => div_mul_cancel₀ _ ha⟩
  obtain ⟨e, he, hp⟩ := exists_gen_pairing BD x k hk c
  refine ⟨e, he, fun V _ _ _ hV ψ gam hg χ hsq => ?_⟩
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing BD.cover χ
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.1
    ((idlAlong_idealSheaf_eq BD χ k' hk').symm.trans (H V hV ψ gam hg χ hsq))
  obtain ⟨e', he', hp'⟩ := exists_gen_pairing BD χ k' hk' w
  refine ⟨e', he', fun z J hJ => ?_⟩
  have hv : toStk z (algebraMap V (FractionRing V) (w * ev χ (BD.U k') hk' (BD.f k'))) =
      toStk z (gam (algebraMap R (FractionRing R) u ^ n)) := by
    rw [mul_comm, hw, map_pow, map_pow gam, hg]
  have hne : IsUnit (toStk z (gam (algebraMap R (FractionRing R) u ^ n))) := ((Ne.isUnit hu').map gam).map _
  have q' : ∀ i, (spMap gam ≫ x) z ∈ BD.U i →
      (gm (Out.jK V) z (LB.wchart (CechPic.dual BD.lb) (fun _ : PUnit => χ) fun _ => i) (e'.s fun _ => i)).val *
        gs (spMap gam ≫ x) z (BD.U i) (BD.f i) = toStk z (gam (algebraMap R (FractionRing R) u ^ n)) := by
    rw [hsq]
    exact fun i hi => (hp' _ (algebraMap V (FractionRing V)) z i hi).trans hv
  have ha : ev x (BD.U k) hk (BD.f k) ≠ 0 := fun h0 => by
    have := q' k (hk trivial)
    rw [gs_spMap_eq gam x _ hk, h0, map_zero, map_zero, mul_zero] at this
    exact hne.ne_zero this.symm
  have q := hp _ gam z _ (hJ (spMap gam ≫ x))
  rw [hc ha] at q
  have q₂ := q' _ (hJ (spMap gam ≫ x))
  rw [val_of e' (Out.jK V) z J (fun _ => J (spMap gam ≫ x)) (fun _ => congrArg J hsq.symm)]
  have hU : IsUnit (gs (spMap gam ≫ x) z (BD.U (J (spMap gam ≫ x))) (BD.f (J (spMap gam ≫ x)))) :=
    isUnit_of_mul_isUnit_right (q ▸ hne)
  exact Units.ext (hU.mul_right_cancel (q.trans q₂.symm))

end GlobalTheory.TraitGen
