import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

theorem pushout_quot {R A B P : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {c : A ⟶ P} {d : B ⟶ P}
    (h : IsPushout a b c d) (hb : Function.Surjective b) :
    Function.Surjective c ∧ ∀ x, c x = 0 → x ∈ (RingHom.ker b.hom).map a.hom := by
  set J := RingHom.ker b.hom
  let Q := CommRingCat.of (A ⧸ J.map a.hom)
  let mk : A ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hker : RingHom.ker b.hom ≤ RingHom.ker ((Ideal.Quotient.mk (J.map a.hom)).comp a.hom) := by
    intro r hr
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  let bQ : B ⟶ Q := CommRingCat.ofHom (RingHom.liftOfSurjective b.hom hb ⟨_, hker⟩)
  have hbQ : ∀ r, bQ (b r) = mk (a r) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  have comm : a ≫ mk = b ≫ bQ := by
    ext r; exact (hbQ r).symm
  let hQ : P ⟶ Q := h.desc mk bQ comm
  have h1 : c ≫ hQ = mk := h.inl_desc _ _ _
  have h2 : d ≫ hQ = bQ := h.inr_desc _ _ _
  have hc : J.map a.hom ≤ RingHom.ker c.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun φ => φ.hom r) h.w
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this, show b.hom r = 0 from hr, map_zero]
  let k : Q ⟶ P := CommRingCat.ofHom (Ideal.Quotient.lift _ c.hom hc)
  have hmk : mk ≫ k = c := by ext x; rfl
  have hid : hQ ≫ k = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, hmk, Category.comp_id]
    · rw [← Category.assoc, h2, Category.comp_id]
      ext y
      obtain ⟨r, rfl⟩ := hb y
      have e1 : k (bQ (b r)) = c (a r) := by rw [hbQ]; rfl
      have e2 := congrArg (fun φ => φ.hom r) h.w
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
      simpa using e1.trans e2
  refine ⟨fun p => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (hQ p)
    refine ⟨x, ?_⟩
    have : k (hQ p) = p := by
      have := congrArg (fun φ => φ.hom p) hid; simpa using this
    rw [← this, ← hx]; rfl
  · have : mk x = hQ (c x) := by rw [← h1]; rfl
    rw [hx, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

def toW {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) : R →+* Γ(X, W) :=
  (p.appLE ⊤ W (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev tq (J : Ideal R) : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

theorem app_fst_tq {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    (hW : IsAffineOpen W) :
    Function.Surjective ((pullback.fst p (tq J)).app W) ∧
      ∀ x, (pullback.fst p (tq J)).app W x = 0 → x ∈ J.map (toW p W) := by
  have H := IsPullback.of_hasPullback p (tq J)
  have hUST : tq J ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ tq J ⁻¹ᵁ ⊤ := le_rfl
  have hUSX : W ≤ p ⁻¹ᵁ ⊤ := le_top
  have hUY : pullback.fst p (tq J) ⁻¹ᵁ W =
      pullback.fst p (tq J) ⁻¹ᵁ W ⊓ pullback.snd p (tq J) ⁻¹ᵁ (tq J ⁻¹ᵁ ⊤) := by
    simp
  have hT : IsAffineOpen (tq J ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) := by
    simpa using isAffineOpen_top (Spec (CommRingCat.of (R ⧸ J)))
  have iso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY (isAffineOpen_top _) hT hW
  have hP := (isIso_pushoutSection_iff H hUST hUSX hUY).1 iso
  have hb0 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))),
      Category.assoc]
  have eR : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
    fun r => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have eR' : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z) = z :=
    fun z => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have eS : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom y) = y :=
    fun y => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hbapp : ∀ z, ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom z =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom
        (Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z)) := fun z => by
    rw [hb0]; rfl
  have hb : Function.Surjective ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST) := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom y)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, ?_⟩
    show ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom _ = y
    rw [hbapp, eR, hr]
    exact eS y
  have hker : RingHom.ker ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom =
      J.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker, hbapp] at hz
      have h1 : Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom hz
        have eS2 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom x) = x :=
          fun x => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
        exact (eS2 _).symm.trans (this.trans (map_zero _))
      rw [← eR' z]
      exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hbapp, eR, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      rfl
  obtain ⟨hs, hk⟩ := pushout_quot hP hb
  have happ : (pullback.fst p (tq J)).appLE W (pullback.fst p (tq J) ⁻¹ᵁ W) le_rfl =
      (pullback.fst p (tq J)).app W := Scheme.Hom.appLE_eq_app _
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← happ]; exact hs
  · have := hk x (by rw [happ]; exact hx)
    rw [hker, Ideal.map_map] at this
    exact this

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

lemma appLE_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

set_option backward.isDefEq.respectTransparency.types false in

theorem app_injective_of_flat_surj {Y Z : Scheme.{0}} (q : Y ⟶ Z) [Flat q] [Surjective q] (V : Z.Opens) :
    Function.Injective (q.app V) := by
  intro a b hab
  refine TopCat.Presheaf.section_ext Z.sheaf V a b fun z hz => ?_
  obtain ⟨y, rfl⟩ := q.surjective z
  have hinj : Function.Injective (q.stalkMap y) := by
    algebraize [(q.stalkMap y).hom]
    have : Module.FaithfullyFlat (Z.presheaf.stalk (q y)) (Y.presheaf.stalk y) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap q y) (q.toLRSHom.prop y)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  show q.stalkMap y (Z.presheaf.germ V (q y) hz a) = q.stalkMap y (Z.presheaf.germ V (q y) hz b)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, hab]

variable {R : Type} [CommRing R] [IsDomain R]

abbrev jF (R : Type) [CommRing R] [IsDomain R] :
    Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

theorem isDominant_jF (R : Type) [CommRing R] [IsDomain R] : IsDominant (jF R) := by
  constructor
  let x : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  have hx : (jF R).base x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal (FractionRing R)) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)]
  have hsub : ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) ⊆
      Set.range (jF R).base :=
    Set.singleton_subset_iff.2 ⟨x, hx⟩
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun y => closure_mono hsub ?_)
  rw [PrimeSpectrum.closure_singleton]
  exact (PrimeSpectrum.mem_zeroLocus _ _).2 (by simp)

theorem app_fst_jF_injective {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (U : X.Opens) :
    Function.Injective ((pullback.fst p (jF R)).app U) := by
  have := isDominant_jF R
  have : IsSchemeTheoreticallyDominant (jF R) := IsSchemeTheoreticallyDominant.of_isDominant _
  exact Scheme.Hom.app_injective _ U

theorem toW_mul_eq_zero {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (V : X.Opens)
    {r : R} (hr : r ≠ 0) {y : Γ(X, V)} (h : toW p V r * y = 0) : y = 0 := by
  set π := pullback.fst p (jF R)
  have hu : IsUnit ((π.app V).hom (toW p V r)) := by
    have e1 : (π.app V).hom (toW p V r) =
        ((pullback.snd p (jF R) ≫ jF R).appLE ⊤ (π ⁻¹ᵁ V) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
      rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq pullback.condition]
    have e2 : (pullback.snd p (jF R) ≫ jF R).appLE ⊤ (π ⁻¹ᵁ V) le_top =
        (jF R).appLE ⊤ (jF R ⁻¹ᵁ ⊤) le_rfl ≫ (pullback.snd p (jF R)).appLE (jF R ⁻¹ᵁ ⊤) (π ⁻¹ᵁ V) le_top := by
      erw [Scheme.Hom.appLE_comp_appLE]
    have e3 : (jF R).appLE ⊤ (jF R ⁻¹ᵁ ⊤) le_rfl =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv := by
      rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
        (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
    have hK : IsUnit (algebraMap R (FractionRing R) r) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]; rfl
    rw [e1, e2, CommRingCat.comp_apply, e3]
    erw [e4]
    exact (hK.map _).map _
  have hinj := app_fst_jF_injective p V
  apply hinj
  have := congrArg (π.app V).hom h
  rw [map_mul, map_zero] at this
  rw [map_zero]
  exact (IsUnit.mul_right_eq_zero hu).1 this

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG
