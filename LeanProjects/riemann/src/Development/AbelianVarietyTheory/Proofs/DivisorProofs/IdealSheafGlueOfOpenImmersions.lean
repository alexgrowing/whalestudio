import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace GlobalTheory.IdealGlue

lemma res_bijective {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (e : U = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

lemma app_bijective {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (W : X.Opens)
    (hW : W ≤ f.opensRange) : Function.Bijective (f.app W).hom := by
  have h2 : f.app W = X.presheaf.map (homOfLE (f.image_preimage_le W)).op ≫
      (f.appIso (f ⁻¹ᵁ W)).hom := by
    rw [← Category.comp_id (f.app W), ← Iso.inv_hom_id (f.appIso (f ⁻¹ᵁ W)), ← Category.assoc,
      f.app_appIso_inv]
    rfl
  rw [h2, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp (f.appIso (f ⁻¹ᵁ W)).commRingCatIsoToRingEquiv.bijective
    (res_bijective _ ?_)
  rw [f.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr hW

noncomputable def loc {P X : Scheme.{u}} (f : P ⟶ X) (J : P.IdealSheafData) (W : X.affineOpens)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) : Ideal Γ(X, W) :=
  (J.ideal ⟨f ⁻¹ᵁ W.1, h⟩).comap (f.app W.1).hom

lemma loc_congr {P X : Scheme.{u}} {f f' : P ⟶ X} (hf : f = f') {J J' : P.IdealSheafData}
    (hJ : J = J') (W : X.affineOpens) (h : IsAffineOpen (f ⁻¹ᵁ W.1))
    (h' : IsAffineOpen (f' ⁻¹ᵁ W.1)) : loc f J W h = loc f' J' W h' := by
  subst hf hJ; rfl

lemma loc_comap {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (W : X.affineOpens) (hW : W.1 ≤ f.opensRange) (h : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc f (I.comap f) W h = I.ideal W := by
  unfold loc
  have hle : (⟨f ''ᵁ f ⁻¹ᵁ W.1, h.image_of_isOpenImmersion f⟩ : X.affineOpens) ≤ W :=
    f.image_preimage_le W.1
  have e1 := I.ideal_comap_of_isOpenImmersion f ⟨f ⁻¹ᵁ W.1, h⟩
  have e2 := I.map_ideal hle
  rw [e1, Ideal.comap_comap, ← CommRingCat.hom_comp, f.app_appIso_inv]
  refine Eq.trans ?_ (Ideal.comap_map_of_bijective _ (res_bijective (f.image_preimage_le W.1) (by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hW)) (I := I.ideal W))
  exact congrArg _ e2.symm

lemma loc_comp {Q' Q X : Scheme.{u}} (g : Q' ⟶ Q) (f : Q ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion f] (J : Q.IdealSheafData) (W : X.affineOpens)
    (hW : W.1 ≤ (g ≫ f).opensRange) (h1 : IsAffineOpen ((g ≫ f) ⁻¹ᵁ W.1))
    (h2 : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc (g ≫ f) (J.comap g) W h1 = loc f J W h2 := by
  have hle : f ⁻¹ᵁ W.1 ≤ g.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hW hy
    refine ⟨z, f.isOpenEmbedding.injective ?_⟩
    simpa using hz
  have := loc_comap g J ⟨f ⁻¹ᵁ W.1, h2⟩ hle
    (by simpa [Scheme.Hom.comp_preimage] using h1)
  unfold loc at this ⊢
  calc _ = (((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩).comap
        (g.app (f ⁻¹ᵁ W.1)).hom).comap (f.app W.1).hom := by
          exact (congrArg (fun φ => Ideal.comap (CommRingCat.Hom.hom φ)
            ((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩)) (Scheme.Hom.comp_app g f W.1)).trans rfl
    _ = _ := congrArg (Ideal.comap (f.app W.1).hom) this

end GlobalTheory.IdealGlue

namespace GlobalTheory.IdealGlue

lemma ideal_transfer {A A' B B' : CommRingCat.{u}} (φ : A ⟶ B) (φ' : A' ⟶ B') (ρ : A ⟶ A')
    (ρ' : B ⟶ B') (hc : ρ ≫ φ' = φ ≫ ρ') (hb : Function.Bijective φ.hom)
    (hb' : Function.Bijective φ'.hom) (𝔞 : Ideal B) :
    (𝔞.comap φ.hom).map ρ.hom = (𝔞.map ρ'.hom).comap φ'.hom := by
  calc (𝔞.comap φ.hom).map ρ.hom
      = (((𝔞.comap φ.hom).map ρ.hom).map φ'.hom).comap φ'.hom :=
        (Ideal.comap_map_of_bijective _ hb').symm
    _ = (((𝔞.comap φ.hom).map φ.hom).map ρ'.hom).comap φ'.hom := by
        rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hc]
    _ = (𝔞.map ρ'.hom).comap φ'.hom := by rw [Ideal.map_comap_of_surjective _ hb.2]

lemma loc_map {P X : Scheme.{u}} (f : P ⟶ X) [IsOpenImmersion f] (J : P.IdealSheafData)
    (W W' : X.affineOpens) (hle : W' ≤ W) (hW : W.1 ≤ f.opensRange)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) (h' : IsAffineOpen (f ⁻¹ᵁ W'.1)) :
    (loc f J W h).map (X.presheaf.map (homOfLE hle).op).hom = loc f J W' h' := by
  have hW' : W'.1 ≤ f.opensRange := (show W'.1 ≤ W.1 from hle).trans hW
  have hJ := J.map_ideal' (U := ⟨f ⁻¹ᵁ W'.1, h'⟩) (V := ⟨f ⁻¹ᵁ W.1, h⟩)
    ((TopologicalSpace.Opens.map f.base).map (homOfLE hle).op.unop).op
  exact (ideal_transfer _ _ _ _ (f.naturality (homOfLE hle).op) (app_bijective f W.1 hW)
    (app_bijective f W'.1 hW') _).trans (congrArg _ hJ)

lemma loc_indep {X : Scheme.{u}} {ι : Type*} (P : ι → Scheme.{u}) (e : ∀ i, P i ⟶ X)
    [∀ i, IsOpenImmersion (e i)] (K : ∀ i, (P i).IdealSheafData)
    (hK : ∀ i j (Q : Scheme.{u}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
      (K i).comap a = (K j).comap b)
    (i j : ι) (W : X.affineOpens) (hi : W.1 ≤ (e i).opensRange) (hj : W.1 ≤ (e j).opensRange)
    (h : IsAffineOpen ((e i) ⁻¹ᵁ W.1)) (h' : IsAffineOpen ((e j) ⁻¹ᵁ W.1)) :
    loc (e i) (K i) W h = loc (e j) (K j) W h' := by
  have hc := pullback.condition (f := e i) (g := e j)
  have hr : W.1 ≤ (pullback.fst (e i) (e j) ≫ e i).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.fst (e i) (e j) ≫ e i) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact ⟨hi hx, hj hx⟩
    exact this
  have hr' : W.1 ≤ (pullback.snd (e i) (e j) ≫ e j).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.snd (e i) (e j) ≫ e j) := by
      rw [← hc]
      exact hr hx
    exact this
  rw [← loc_comp (pullback.fst (e i) (e j)) (e i) (K i) W hr
      (W.2.preimage_of_isOpenImmersion _ hr) h,
    ← loc_comp (pullback.snd (e i) (e j)) (e j) (K j) W hr'
      (W.2.preimage_of_isOpenImmersion _ hr') h']
  exact loc_congr hc (hK i j _ _ _ hc) _ _ _

theorem idealSheaf_glue_of_openImmersions :
    (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) →
    ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X),
      (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) →
      ∀ (K : ∀ i, (P i).IdealSheafData),
      (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
        (K i).comap a = (K j).comap b) →
      ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  intro hA X ι P e he hcov K hK
  classical
  have haff : ∀ i (W : X.affineOpens), W.1 ≤ (e i).opensRange → IsAffineOpen ((e i) ⁻¹ᵁ W.1) :=
    fun i W hW => W.2.preimage_of_isOpenImmersion (e i) hW
  let k : ∀ W : X.affineOpens, Ideal Γ(X, W) := fun W =>
    if hex : ∃ i, W.1 ≤ (e i).opensRange then
      loc (e hex.choose) (K hex.choose) W (haff _ W hex.choose_spec) else ⊤
  have hk : ∀ i (W : X.affineOpens) (hW : W.1 ≤ (e i).opensRange),
      k W = loc (e i) (K i) W (haff i W hW) := by
    intro i W hW
    have hex : ∃ i, W.1 ≤ (e i).opensRange := ⟨i, hW⟩
    simp only [k, dif_pos hex]
    exact loc_indep P e K hK _ _ W hex.choose_spec hW _ _
  have hcov' : ∀ x : X, ∃ W : X.affineOpens, ∃ i, W.1 ≤ (e i).opensRange ∧ x ∈ W.1 := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact ⟨⟨W, hW⟩, i, hWle, hxW⟩
  obtain ⟨I, hI⟩ := hA {W | ∃ i, W.1 ≤ (e i).opensRange}
    (fun W ⟨i, hi⟩ W' hW' => ⟨i, (show W'.1 ≤ W.1 from hW').trans hi⟩)
    (fun x => by
      obtain ⟨W, i, hi, hx⟩ := hcov' x
      exact ⟨W, ⟨i, hi⟩, hx⟩)
    k
    (fun W ⟨i, hi⟩ W' hW' => by
      have hi' : W'.1 ≤ (e i).opensRange := (show W'.1 ≤ W.1 from hW').trans hi
      rw [hk i W hi, hk i W' hi']
      exact loc_map (e i) (K i) W W' hW' hi _ _)
  refine ⟨I, fun i => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // W.1 ≤ (e i).opensRange})
    (fun W => ⟨(e i) ⁻¹ᵁ W.1.1, haff i W.1 W.2⟩) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨W, hW, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hyW⟩
  · intro W
    apply Ideal.comap_injective_of_surjective _ (app_bijective (e i) W.1.1 W.2).2
    have h1 := loc_comap (e i) I W.1 W.2 (haff i W.1 W.2)
    have h2 := hk i W.1 W.2
    have h3 := hI W.1 ⟨i, W.2⟩
    exact h1.trans (h3.trans h2)

end GlobalTheory.IdealGlue
