import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPowStatement

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Pair

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) =
      x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

def strHom {R : Type} [CommRing R] (X : Over (Sp R)) (V : X.left.Opens) : R →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ V (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)).hom

theorem fromSpec_over {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (strHom X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Sp R)) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]; rfl

theorem chartHom_comp_strHom {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by
  have e : spMap ((chartHom V u hu).comp (strHom X V)) = spMap f := by
    rw [spMap_comp', ← fromSpec_over X hV, ← Category.assoc, chart_rebuild, hf]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem smooth_strHom {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ V le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top (Sp R)) hV le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact h2.comp h1

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (c : R) : Function.Surjective (Localization.awayMap π c) :=
  (IsLocalization.Away.map_surjective_iff _ _ π c).2 fun y =>
    let ⟨x, hx⟩ := hπ y; ⟨x, 0, by simp [hx]⟩

theorem ker_awayMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    RingHom.ker (Localization.awayMap π c) = (RingHom.ker π).map (algebraMap R (Localization.Away c)) := by
  exact IsLocalization.ker_map (S := Localization.Away c) (Localization.Away (π c)) π
    (M := Submonoid.powers c) (Submonoid.map_powers π c)

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hsq : RingHom.ker π ^ 2 = ⊥) (c : R) : RingHom.ker (Localization.awayMap π c) ^ 2 = ⊥ := by
  rw [ker_awayMap, ← Ideal.map_pow, hsq, Ideal.map_bot]

theorem awayMap_comp_algebraMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π :=
  IsLocalization.map_comp _

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem red_comp {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (c d : R) (hcd : c ∣ d) (e : Sp (Localization.Away c) ⟶ Y)
    (he : spMap (Localization.awayMap π c) ≫ e = spMap (algebraMap R₀ (Localization.Away (π c))) ≫ g₀)
    (r : Localization.Away c →+* Localization.Away d)
    (hr : r.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away d)) :
    spMap (Localization.awayMap π d) ≫ spMap r ≫ e =
      spMap (algebraMap R₀ (Localization.Away (π d))) ≫ g₀ := by
  have hu : IsUnit (algebraMap R₀ (Localization.Away (π d)) (π c)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd π hcd)) (IsLocalization.Away.algebraMap_isUnit (π d))
  let h : Localization.Away (π c) →+* Localization.Away (π d) := IsLocalization.Away.lift (π c) hu
  have e1 : (Localization.awayMap π d).comp r = h.comp (Localization.awayMap π c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [RingHom.comp_assoc, hr, awayMap_comp_algebraMap, RingHom.comp_assoc, awayMap_comp_algebraMap,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  rw [← Category.assoc, ← spMap_comp', e1, spMap_comp', Category.assoc, he, ← Category.assoc,
    ← spMap_comp', IsLocalization.Away.lift_comp]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem equiv_restrict {R : Type} [CommRing R] (a b : R)
    (eP : Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b))
    (ρ : Localization.Away a →+* Localization.Away (a * b))
    (hρ : ρ.comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)))
    (y : Localization.Away a) :
    eP (ρ y) = algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) y := by
  have e : (eP.toAlgHom : Localization.Away (a * b) →+* _).comp ρ =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [RingHom.comp_assoc, hρ, eP.toAlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq _ _ _
  exact RingHom.congr_fun e y

theorem exists_awayEquiv {R : Type} [CommRing R] (a b : R) :
    Nonempty (Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b)) :=
  ⟨IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _⟩

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem comp_over {Y : Scheme.{0}} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (e : Sp B ⟶ Y)
    (p : Y ⟶ Sp A) (f : A →+* B) (he : e ≫ p = spMap f) (r : B →+* C) (g : A →+* C) (hr : r.comp f = g) :
    (spMap r ≫ e) ≫ p = spMap g := by
  rw [Category.assoc, he, ← spMap_comp', hr]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue

open GlobalTheory.SecGlue.Pair in
set_option maxHeartbeats 1000000 in

theorem exists_pair_lift_comb : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  intro R R₀ _ _ π hπ hsq X hX g₀ hg₀ a b V hV ea hea hea₀ heaV eb heb heb₀
  haveI := hX
  letI : Algebra R Γ(X.left, V) := (strHom X V).toAlgebra
  haveI : Algebra.Smooth R Γ(X.left, V) := smooth_strHom X hV

  have hρ : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b).comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b)
  have hρ' : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a).comp (algebraMap R (Localization.Away b)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a)
  generalize IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b = ρ at hρ ⊢
  generalize IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a = ρ' at hρ' ⊢
  have hred : spMap (Localization.awayMap π (a * b)) ≫ spMap ρ' ≫ eb =
      spMap (Localization.awayMap π (a * b)) ≫ spMap ρ ≫ ea :=
    (red_comp π g₀ b (a * b) (dvd_mul_left b a) eb heb₀ ρ' hρ').trans
      (red_comp π g₀ a (a * b) (dvd_mul_right a b) ea hea₀ ρ hρ).symm
  have h2 : (spMap ρ ≫ ea) ⁻¹ᵁ V = ⊤ := preimage_spMap_comp_eq_top ρ heaV
  have hbV : (spMap ρ' ≫ eb) ⁻¹ᵁ V = ⊤ :=
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening (Localization.Away (a * b)) (Localization.Away (π (a * b))) (Localization.awayMap π (a * b))
      (awayMap_surjective π hπ _) (ker_awayMap_sq π hsq _) X.left (spMap ρ' ≫ eb) (spMap ρ ≫ ea) hred V).trans h2

  let φ : Γ(X.left, V) →ₐ[R] Localization.Away a :=
    { chartHom V ea heaV with
      commutes' := fun r => RingHom.congr_fun (chartHom_comp_strHom X hV _ ea heaV hea) r }

  obtain ⟨eP⟩ := exists_awayEquiv a b
  have hePc : (eP.toAlgHom : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
      (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) :=
    eP.toAlgHom.comp_algebraMap
  have heP := equiv_restrict a b eP ρ hρ
  have heb' : (spMap ρ' ≫ eb) ≫ X.hom = spMap (algebraMap R (Localization.Away (a * b))) :=
    comp_over eb X.hom _ heb ρ' _ hρ'
  let ψ : Γ(X.left, V) →ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b) :=
    { (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp (chartHom V (spMap ρ' ≫ eb) hbV) with
      commutes' := fun r => by
        show eP (chartHom V (spMap ρ' ≫ eb) hbV (strHom X V r)) = _
        rw [← RingHom.comp_apply, chartHom_comp_strHom X hV _ _ hbV heb', AlgEquiv.commutes] }
  have hJ : RingHom.ker (Localization.awayMap π a) ^ 2 = ⊥ := ker_awayMap_sq π hsq a
  have hcond : ∀ x, ψ x - algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) ∈
      (RingHom.ker (Localization.awayMap π a)).map (algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))) := by
    intro x
    have hd : chartHom V (spMap ρ' ≫ eb) hbV x - chartHom V (spMap ρ ≫ ea) h2 x ∈
        RingHom.ker (Localization.awayMap π (a * b)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero,
        ← chartHom_spMap_comp V _ _ hbV (preimage_spMap_comp_eq_top _ hbV),
        ← chartHom_spMap_comp V _ _ h2 (preimage_spMap_comp_eq_top _ h2)]
      exact RingHom.congr_fun (chartHom_congr V hred _ _) x
    rw [ker_awayMap] at hd
    have h3 := Ideal.mem_map_of_mem (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)) hd
    rw [Ideal.map_map, show (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
        (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) from
        RingHom.ext fun r => eP.commutes r, map_sub] at h3
    rw [ker_awayMap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have e2 : algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) =
        eP (chartHom V (spMap ρ ≫ ea) h2 x) := by
      rw [chartHom_spMap_comp V ρ ea heaV h2 x, heP]
      rfl
    rw [e2]
    exact h3
  obtain ⟨N₀, hN⟩ := GlobalTheory.T.exists_sqZero_extend_localizationAway_pow R Γ(X.left, V) (Localization.Away a) (RingHom.ker (Localization.awayMap π a)) hJ (algebraMap R (Localization.Away a) b) φ ψ hcond
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨χ, hχJ, hχ⟩ := hN N hN'
  have htop := fromSpec_comp_top hV (χ : Γ(X.left, V) →+* Localization.Away a)
  refine ⟨spMap (χ : Γ(X.left, V) →+* Localization.Away a) ≫ hV.fromSpec, ?_, ?_, htop, ?_⟩
  · rw [Category.assoc, fromSpec_over, ← spMap_comp']
    exact congrArg spMap (RingHom.ext fun r => χ.commutes r)
  · rw [← hea₀, ← chart_rebuild hV ea heaV, ← Category.assoc, ← Category.assoc, ← spMap_comp',
      ← spMap_comp']
    refine congrArg (fun f => spMap f ≫ hV.fromSpec) (RingHom.ext fun x => ?_)
    have := hχJ x
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · refine ⟨h2, preimage_spMap_comp_eq_top ρ htop, fun i => by rw [Matrix.cons_val_fin_one]; exact hbV, fun x => ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [chartHom_spMap_comp V ρ _ htop, chartHom_fromSpec hV _ htop, chartHom_spMap_comp V ρ ea heaV]
    apply eP.injective
    rw [map_add, map_mul, map_sub, map_pow, heP, heP, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))]
    exact hχ x

end GlobalTheory.SecGlue
