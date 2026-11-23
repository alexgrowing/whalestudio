import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

private theorem comap_ideal_eq_ker_pullbackFst (I : Y.IdealSheafData) (f : X ⟶ Y)
    (V : X.affineOpens) :
    (I.comap f).ideal V
      = RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hc : I.comap f = Scheme.Hom.ker (Limits.pullback.fst f I.subschemeι) := rfl
  rw [hc, ← map_bot, ideal_map_of_isAffineHom,
    show ((⊥ : (Limits.pullback f I.subschemeι).IdealSheafData).ideal) = ⊥ from ideal_bot]
  exact (RingHom.ker_eq_comap_bot _).symm

private theorem appLE_congr_hom {Z W : Scheme.{u}} {g₁ g₂ : Z ⟶ W} (h : g₁ = g₂)
    (U : W.Opens) (V : Z.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) :
    g₁.appLE U V e₁ = g₂.appLE U V (h ▸ e₁) := by
  subst h; rfl

private theorem map_appLE_le_ker_pullbackFst (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) ≤
      RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hcond : Limits.pullback.fst f I.subschemeι ≫ f
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι := Limits.pullback.condition
  have h2 : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ (U : Y.Opens))
      = (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    have h3 := congrArg
      (fun g : (Limits.pullback f I.subschemeι) ⟶ Y => g ⁻¹ᵁ (U : Y.Opens)) hcond
    simpa using h3
  have hle : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)
      ≤ (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    rw [← h2]
    intro x hx
    exact e hx
  have happ : f.appLE (U : Y.Opens) (V : X.Opens) e
        ≫ (Limits.pullback.fst f I.subschemeι).app (V : X.Opens)
      = I.subschemeι.app (U : Y.Opens)
        ≫ (Limits.pullback.snd f I.subschemeι).appLE (I.subschemeι ⁻¹ᵁ (U : Y.Opens))
            ((Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)) hle := by
    rw [← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
      ← Scheme.Hom.appLE_eq_app I.subschemeι, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hcond]
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have hker : (I.subschemeι.app (U : Y.Opens)).hom a = 0 := by
    have hd := I.ker_subschemeι_app U
    rw [← RingHom.mem_ker, hd]
    exact ha
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, happ, CommRingCat.hom_comp,
    RingHom.comp_apply, hker, map_zero]

private theorem appLE_top_eq_appTop (f : X ⟶ Y) (e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0 = f.appTop := by
  have h1 : X.presheaf.map (homOfLE e0).op = 𝟙 Γ(X, ⊤) := X.presheaf.map_id (op (⊤ : X.Opens))
  calc f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0
      = f.app (⊤ : Y.Opens) ≫ X.presheaf.map (homOfLE e0).op := rfl
    _ = f.app (⊤ : Y.Opens) ≫ 𝟙 Γ(X, ⊤) := by rw [h1]
    _ = f.appTop := Category.comp_id _

theorem ofIdealTop_ideal_top {Z : Scheme.{u}} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [equivOfIsAffine_symm_apply, equivOfIsAffine_apply] at h
  exact h

private theorem exists_hom_comp_eq_appLE_comp (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (hq : Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U)
      ≤ RingHom.ker q.hom) :
    ∃ ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C,
      I.subschemeι.app (U : Y.Opens) ≫ ψ = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q := by
  refine ⟨(I.subschemeObjIso U).hom ≫ CommRingCat.ofHom
      (Ideal.Quotient.lift (I.ideal U)
        (q.hom.comp (f.appLE (U : Y.Opens) (V : X.Opens) e).hom) ?_), ?_⟩
  · intro a ha
    have h := hq (Ideal.mem_map_of_mem _ ha)
    rw [RingHom.mem_ker] at h
    exact h
  · rw [subschemeι_app, Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    rfl

private theorem exists_hom_pullbackFst_app_comp_eq (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C)
    (hring : I.subschemeι.app (U : Y.Opens) ≫ ψ
      = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q) :
    ∃ θ : Γ(Limits.pullback f I.subschemeι,
        Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) ⟶ C,
      (Limits.pullback.fst f I.subschemeι).app (V : X.Opens) ≫ θ = q := by
  have hV : IsAffineOpen (V : X.Opens) := V.2
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hf := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
  have hι := IsAffineOpen.SpecMap_appLE_fromSpec I.subschemeι hU
      (hU.preimage I.subschemeι) (le_refl (I.subschemeι ⁻¹ᵁ (U : Y.Opens)))
  have hsq : (Spec.map q ≫ hV.fromSpec) ≫ f
      = (Spec.map ψ ≫ (hU.preimage I.subschemeι).fromSpec) ≫ I.subschemeι := by
    rw [Category.assoc, Category.assoc, ← hf, ← hι, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, Scheme.Hom.appLE_eq_app, hring]
  obtain ⟨g, hlift⟩ : ∃ g : Spec C ⟶ Limits.pullback f I.subschemeι,
      g ≫ Limits.pullback.fst f I.subschemeι = Spec.map q ≫ hV.fromSpec :=
    ⟨Limits.pullback.lift _ _ hsq, Limits.pullback.lift_fst _ _ _⟩
  have hpre : (⊤ : (Spec C).Opens)
      ≤ g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) := by
    have h3 := congrArg (fun h : Spec C ⟶ X => h ⁻¹ᵁ (V : X.Opens)) hlift
    have h4 : g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
        = Spec.map q ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ (V : X.Opens)) := by simpa using h3
    rw [h4, hV.fromSpec_preimage_self]
    simp
  have e₁ : (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) ≤ hV.fromSpec ⁻¹ᵁ (V : X.Opens) :=
    le_of_eq (hV.fromSpec_preimage_self).symm
  have e₂ : (⊤ : (Spec C).Opens)
      ≤ Spec.map q ⁻¹ᵁ (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) := by simp
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map q) hV.fromSpec (V : X.Opens)
      (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) (⊤ : (Spec C).Opens) e₁ e₂
  have h0 : ∀ i : (op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens))
      ⟶ op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens),
      (Spec Γ(X, (V : X.Opens))).presheaf.map i = 𝟙 _ := by
    intro i
    have hi : i = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
  have hdef : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = hV.fromSpec.app (V : X.Opens)
        ≫ (Spec Γ(X, (V : X.Opens))).presheaf.map (homOfLE e₁).op := rfl
  have ha : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv := by
    rw [hdef, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← op_comp,
      h0, Category.comp_id]
  have hb : (Spec.map q).appTop
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).hom ≫ q ≫ (Scheme.ΓSpecIso C).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  refine ⟨g.appLE (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
      (⊤ : (Spec C).Opens) hpre ≫ (Scheme.ΓSpecIso C).hom, ?_⟩
  rw [← Category.assoc, ← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
    Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hlift, ← hsplit, ha, appLE_top_eq_appTop, hb]
  simp

private theorem ker_pullbackFst_le_map_appLE (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom ≤
      Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) := by
  obtain ⟨C, q, hq⟩ : ∃ (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C),
      RingHom.ker q.hom = Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) :=
    ⟨_, CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U))), Ideal.mk_ker⟩
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_appLE_comp I f U V e C q (le_of_eq hq.symm)
  obtain ⟨θ, hθ⟩ := exists_hom_pullbackFst_app_comp_eq I f U V e C q ψ hψ
  rw [← hq]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← hθ, CommRingCat.hom_comp, RingHom.comp_apply, hx, map_zero]

theorem comap_ideal_eq_map_appLE (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom := by
  rw [comap_ideal_eq_ker_pullbackFst I f V]
  exact le_antisymm (ker_pullbackFst_le_map_appLE I f U V e)
    (map_appLE_le_ker_pullbackFst I f U V e)

theorem map_appLE_le_comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    (I.ideal U).map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom ≤ (I.comap f).ideal V :=
  ge_of_eq (comap_ideal_eq_map_appLE I f U V e)

theorem comap_ideal_top_eq_map_appTop [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  rw [comap_ideal_eq_map_appLE I f ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩ e0]
  exact congrArg
    (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
    (appLE_top_eq_appTop f e0)

theorem comap_ofIdealTop [IsAffine X] [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (ofIdealTop J).comap f = ofIdealTop (J.map f.appTop.hom) := by
  have h : ((ofIdealTop J).comap f).ideal ⟨⊤, isAffineOpen_top X⟩
      = (ofIdealTop (J.map f.appTop.hom)).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, ofIdealTop_ideal_top]
  exact (equivOfIsAffine (X := X)).injective h

theorem appLE_mem_comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) {x : Γ(Y, (U : Y.Opens))}
    (hx : x ∈ I.ideal U) :
    (f.appLE (U : Y.Opens) (V : X.Opens) e).hom x ∈ (I.comap f).ideal V :=
  map_appLE_le_comap_ideal I f U V e (Ideal.mem_map_of_mem _ hx)

theorem comap_ideal_eq_span_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) (s : Set Γ(Y, (U : Y.Opens)))
    (hs : I.ideal U = Ideal.span s) :
    (I.comap f).ideal V
      = Ideal.span ((f.appLE (U : Y.Opens) (V : X.Opens) e).hom '' s) := by
  rw [comap_ideal_eq_map_appLE I f U V e, hs, Ideal.map_span]

theorem comap_iSup {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Sort*} (I : ι → Y.IdealSheafData) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f :=
  (map_gc f).l_iSup

theorem comap_ι_eq_top_iff_ideal_eq_top {Y : Scheme.{u}} (I : Y.IdealSheafData) {V : Y.Opens}
    (hV : IsAffineOpen V) : I.comap V.ι = ⊤ ↔ I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : ∀ U : V.toScheme.affineOpens, (⊤ : V.toScheme.IdealSheafData).ideal U = ⊤ := by
    intro U
    simp
  have e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have himg : V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V := by simp
  have hiso : ∀ U : Y.Opens, U = V.ι ''ᵁ (⊤ : V.toScheme.Opens) →
      ∀ e' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ U,
        IsIso (V.ι.appLE U (⊤ : V.toScheme.Opens) e') := by
    rintro U rfl e'
    rw [← Scheme.Hom.appIso_hom' V.ι (⊤ : V.toScheme.Opens)]
    infer_instance
  obtain ⟨φ, hφ, hmap⟩ : ∃ φ : Γ(Y, V) ⟶ Γ(V.toScheme, ⊤), IsIso φ ∧
      (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (I.ideal ⟨V, hV⟩).map φ.hom :=
    ⟨V.ι.appLE V (⊤ : V.toScheme.Opens) e, hiso V himg.symm e,
      comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e⟩
  have hcomp : (CommRingCat.Hom.hom (CategoryTheory.inv φ)).comp (CommRingCat.Hom.hom φ)
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id]
  constructor
  · intro h
    rw [h, htop] at hmap
    have h3 : ((I.ideal ⟨V, hV⟩).map φ.hom).map (CategoryTheory.inv φ).hom
        = I.ideal ⟨V, hV⟩ := by
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    rw [← hmap, Ideal.map_top] at h3
    exact h3.symm
  · intro h
    have h2 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ := by
      rw [hmap, h, Ideal.map_top, htop]
    exact (equivOfIsAffine (X := V.toScheme)).injective h2

theorem ofIdealTop_mul [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I * J) = ofIdealTop I * ofIdealTop J := by
  ext U : 2
  exact Ideal.map_mul _ _ _

theorem comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_iSup_eq_top
    (fun W : {W : X.affineOpens // ∃ U : Y.affineOpens, (W : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)} =>
      W.1) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top,
      Set.eq_univ_iff_forall, Set.mem_iUnion]
    intro x
    obtain ⟨W, hxW⟩ := Scheme.exists_affineOpens_mem (f.base x)
    obtain ⟨V, hxV, hVW⟩ :
        ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ f ⁻¹ᵁ (W : Y.Opens) :=
      Scheme.exists_affineOpens_mem_le hxW
    exact ⟨⟨V, W, hVW⟩, hxV⟩
  · rintro ⟨V, W, hVW⟩
    show ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V
    rw [comap_ideal_eq_map_appLE (I * J) f W V hVW]
    simp only [ideal_mul, Pi.mul_apply]
    rw [Ideal.map_mul, comap_ideal_eq_map_appLE I f W V hVW,
      comap_ideal_eq_map_appLE J f W V hVW]

theorem comap_pow (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, comap_mul, ih]

theorem mem_support_comap {f : X ⟶ Y} {I : Y.IdealSheafData} {x : X} :
    x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by
  constructor
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hx
    exact hx
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx

theorem ne_top_of_mem_support (J : Y.IdealSheafData) (x : ↥Y) (hx : x ∈ J.support) : J ≠ ⊤ := by
  intro hc
  have hb : J.support = ⊥ :=
    (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff J).mpr hc
  have hx2 : x ∈ (J.support : Set ↥Y) := hx
  rw [hb] at hx2
  simp at hx2

theorem eq_top_iff_support_eq_empty {X : Scheme.{u}} (I : X.IdealSheafData) :
    I = ⊤ ↔ (I.support : Set X) = ∅ := by
  rw [← support_eq_bot_iff, SetLike.ext'_iff]
  simp

theorem support_nonempty_iff_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) :
    (I.support : Set X).Nonempty ↔ I ≠ ⊤ := by
  rw [ne_eq, eq_top_iff_support_eq_empty, Set.nonempty_iff_ne_empty, ne_eq]

theorem notMem_support_of_comap_ι_eq_top (I : Y.IdealSheafData) {U : Y.Opens}
    (h : I.comap U.ι = ⊤) {x : Y} (hxU : x ∈ U) : x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

private theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (g : Γ(X, U)) :
    x ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec ⁻¹ᵁ (X.basicOpen g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  constructor
  · intro h
    rw [← h1] at h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ (X.basicOpen g) := h
    rw [h2] at h3
    exact (PrimeSpectrum.mem_basicOpen g _).mp h3
  · intro h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g :=
      (PrimeSpectrum.mem_basicOpen g _).mpr h
    rw [← h2] at h3
    have h4 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g := h3
    rwa [h1] at h4

theorem mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx,
    Scheme.mem_zeroLocus_iff]
  constructor
  · intro h
    rw [SetLike.le_def]
    intro f hf
    have hb := h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f] at hb
    exact not_not.mp hb
  · intro h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f]
    exact not_not.mpr (h hf)

theorem comap_ι_comp_eq_of_comap_ι_eq (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hle : U ≤ f ⁻¹ᵁ V) (I J : Y.IdealSheafData)
    (h : I.comap V.ι = J.comap V.ι) : I.comap (U.ι ≫ f) = J.comap (U.ι ≫ f) := by
  have hfac : X.homOfLE hle ≫ ((f ∣_ V) ≫ V.ι) = U.ι ≫ f := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  have e : ∀ K : Y.IdealSheafData,
      ((K.comap V.ι).comap (f ∣_ V)).comap (X.homOfLE hle) = K.comap (U.ι ≫ f) := by
    intro K
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, CategoryTheory.Category.assoc, hfac]
  rw [← e I, ← e J, h]

theorem comap_listProd {X Y : Scheme.{u}} (f : X ⟶ Y) (L : List Y.IdealSheafData) :
    L.prod.comap f = (L.map (·.comap f)).prod := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact comap_top f
  | cons D E ih => simp only [List.map_cons, List.prod_cons, comap_mul, ih]

theorem comap_finset_prod {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (F : ι → Y.IdealSheafData) :
    (∏ i ∈ s, F i).comap f = ∏ i ∈ s, (F i).comap f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact comap_top f
  · intro a t ha ih
    simp only [Finset.prod_insert ha, comap_mul, ih]

private theorem isReduced_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : _root_.IsReduced B) : _root_.IsReduced A := by
  have := h
  exact ⟨fun a ha => e.injective (by simpa using (ha.map (e : A →+* B)).eq_zero)⟩

private theorem isReduced_stalk_of_radical (I : X.IdealSheafData)
    (hrad : ∀ U : X.affineOpens, (I.ideal U).IsRadical) (y : ↥I.subscheme) :
    _root_.IsReduced (I.subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU⟩ := Scheme.exists_affineOpens_mem (I.subschemeι.base y)
  have hUaff : IsAffineOpen (U : X.Opens) := U.2
  have hy : y ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens) := hU
  have hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ (U : X.Opens)) :=
    IsAffineOpen.preimage hUaff I.subschemeι
  have hquot := (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hrad U)
  have hGamma := isReduced_of_ringEquiv (I.subschemeObjIso U).commRingCatIsoToRingEquiv hquot
  have hTop := isReduced_of_ringEquiv (Scheme.Opens.topIso
    (I.subschemeι ⁻¹ᵁ (U : X.Opens))).commRingCatIsoToRingEquiv hGamma
  have : IsAffine (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) := hV
  have := hTop
  have : IsReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) :=
    isReduced_of_isAffine_isReduced _
  have key : _root_.IsReduced
      ((↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}).presheaf.stalk
        (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))) :=
    isReduced_stalk_of_isReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u})
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))
  exact isReduced_of_ringEquiv
    (Scheme.Opens.stalkIso (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))).symm.commRingCatIsoToRingEquiv key

theorem isReduced_subscheme_vanishingIdeal
    (W : Scheme.{u}) (Z : TopologicalSpace.Closeds W) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have : ∀ y : ↥((Scheme.IdealSheafData.vanishingIdeal Z).subscheme),
      _root_.IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk y) := by
    intro y
    refine isReduced_stalk_of_radical _ ?_ y
    intro U
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact isReduced_of_isReduced_stalk _

theorem comap_subschemeι_self {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap I.subschemeι = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := comap_map_le (⊥ : I.subscheme.IdealSheafData) I.subschemeι
  rwa [map_bot, ker_subschemeι] at h

end AlgebraicGeometry.Scheme.IdealSheafData

namespace FunctorialResolution.Blowup

theorem noetherianSpace_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    I.subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

instance instNoetherianSpaceSubscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  noetherianSpace_subscheme I

theorem idealSheafData_prod_nil (X : Scheme.{u}) :
    ([] : List X.IdealSheafData).prod = ⊤ := by
  rw [List.prod_nil]
  rfl

theorem idealSheafData_prod_cons (X : Scheme.{u}) (D : X.IdealSheafData)
    (E : List X.IdealSheafData) : (D :: E).prod = D * E.prod :=
  List.prod_cons

theorem comap_ker_comp_of_isOpenImmersion {A B C : Scheme.{u}} (j : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion f] [QuasiCompact j] [QuasiCompact (j ≫ f)] :
    (j ≫ f).ker.comap f = j.ker := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ V.1) := V.2.image_of_isOpenImmersion f
  have hpre : f ⁻¹ᵁ (f ''ᵁ V.1) = V.1 := f.preimage_image_eq V.1
  have e : (V : B.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ V.1) := hpre.ge
  have hopeq : j ⁻¹ᵁ V.1 = (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := by
    show j ⁻¹ᵁ V.1 = j ⁻¹ᵁ (f ⁻¹ᵁ (f ''ᵁ V.1))
    rw [hpre]
  have hop : j ⁻¹ᵁ V.1 ≤ (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := hopeq.le
  have key : f.appLE (f ''ᵁ V.1) V.1 e ≫ j.app V.1
      = (j ≫ f).app (f ''ᵁ V.1) ≫ A.presheaf.map (homOfLE hop).op := by
    rw [Scheme.Hom.app_eq_appLE j]
    exact Scheme.Hom.appLE_comp_appLE j f (f ''ᵁ V.1) V.1 (j ⁻¹ᵁ V.1) e le_rfl
  have keyr : ∀ x, (CommRingCat.Hom.hom (j.app V.1))
        ((CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) x)
      = (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op))
        ((CommRingCat.Hom.hom ((j ≫ f).app (f ''ᵁ V.1))) x) := by
    intro x
    have h' := congrArg (fun m => (CommRingCat.Hom.hom m) x) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  have hρ : ∀ y, (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op)) y = 0 → y = 0 := by
    intro y hy
    have hcomp : A.presheaf.map (homOfLE hop).op ≫ A.presheaf.map (homOfLE hopeq.ge).op
        = 𝟙 (A.presheaf.obj (Opposite.op ((j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1)))) := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp,
        Subsingleton.elim (homOfLE hopeq.ge ≫ homOfLE hop) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
    have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) y) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      hy, map_zero] at h2
    exact h2.symm
  have hφ : Function.Surjective (CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) := by
    have : IsIso (f.appLE (f ''ᵁ V.1) V.1 e) := by
      rw [← Scheme.Hom.appIso_hom' f V.1]
      infer_instance
    intro y
    refine ⟨(CommRingCat.Hom.hom (inv (f.appLE (f ''ᵁ V.1) V.1 e))) y, ?_⟩
    have h3 := congrArg (fun m => (CommRingCat.Hom.hom m) y)
      (IsIso.inv_hom_id (f.appLE (f ''ᵁ V.1) V.1 e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ f ⟨f ''ᵁ V.1, hU⟩ V e,
    Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, keyr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    obtain ⟨x, rfl⟩ := hφ y
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker] at hy ⊢
    exact hρ _ ((keyr x).symm.trans hy)

end FunctorialResolution.Blowup

namespace AlgebraicGeometry.Scheme.IdealSheafData

theorem exists_iso_subscheme_comap_of_isIso {Y Y' : Scheme.{u}} (g : Y ⟶ Y') [IsIso g]
    (I : Y'.IdealSheafData) :
    ∃ m : (I.comap g).subscheme ⟶ I.subscheme,
      IsIso m ∧ m ≫ I.subschemeι = (I.comap g).subschemeι ≫ g := by
  have : QuasiCompact (I.comap g).subschemeι := inferInstance
  have : QuasiCompact ((I.comap g).subschemeι ≫ g) := inferInstance
  have hq := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (I.comap g).subschemeι g
  rw [Scheme.IdealSheafData.ker_subschemeι] at hq
  have e1 : ∀ J : Y'.IdealSheafData, (J.comap g).comap (inv g) = J := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have hkk : ((I.comap g).subschemeι ≫ g).ker = I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      ← e1 (((I.comap g).subschemeι ≫ g).ker), hq, e1]
  refine ⟨IsClosedImmersion.lift I.subschemeι ((I.comap g).subschemeι ≫ g)
      (le_of_eq hkk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq ((I.comap g).subschemeι ≫ g) I.subschemeι _
    (IsClosedImmersion.lift_fac _ _ _) hkk

end AlgebraicGeometry.Scheme.IdealSheafData
