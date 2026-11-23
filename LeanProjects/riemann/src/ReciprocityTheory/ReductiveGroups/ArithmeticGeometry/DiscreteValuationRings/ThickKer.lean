import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] {X : Scheme.{0}}

def strMap (p : X ⟶ Sp V) (U : X.Opens) : V →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom

theorem constFn_eq_strMap (p : X ⟶ Sp V) (U : X.Opens) (a : V) : constFn p U a = strMap p U a := rfl

theorem fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem appLE_top_eq {Y W : Scheme.{0}} (f : Y ⟶ W) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

theorem mem_map_of_app_fst_eq_zero (p : X ⟶ Sp V) (J : Ideal V) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (ha : ((pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom a = 0) :
    a ∈ J.map (strMap p U) := by
  let I₀ : Ideal Γ(X, U) := J.map (strMap p U)
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I₀ := Ideal.Quotient.mk I₀
  let ψ : V ⧸ J →+* Γ(X, U) ⧸ I₀ := Ideal.quotientMap I₀ (strMap p U) Ideal.le_comap_map
  let z : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  have hz : ⊤ ≤ z ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : z.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : z.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp, fromSpec_appLE_top]
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (z.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  have m1 : (z ≫ p).appTop = p.appLE ⊤ U le_top ≫ z.appLE U ⊤ hz :=
    ((Scheme.Hom.appLE_comp_appLE z p ⊤ U ⊤ le_top hz).trans (appLE_top_eq _ _)).symm
  have m5 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))).symm
  have m6 : (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)).symm
  have e5 : ∀ c : V, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J c) :=
    fun c => congrArg (fun φ => φ.hom c) m5
  have e6 : ∀ c : V ⧸ J, (Spec.map (CommRingCat.ofHom ψ)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (ψ c) :=
    fun c => congrArg (fun φ => φ.hom c) m6
  have hsq : z ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1
    ext b
    show (z ≫ p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b) =
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    rw [m1, Scheme.Hom.comp_appTop]
    show (z.appLE U ⊤ hz).hom ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b))
    rw [k1, e5, e6, Ideal.quotientMap_mk]
    rfl
  let l := pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) hsq
  have hl : l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = z := pullback.lift_fst _ _ _
  have tr : ∀ (w : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X) (hw : w = z) (e : ⊤ ≤ w ⁻¹ᵁ U),
      (w.appLE U ⊤ e).hom a = (z.appLE U ⊤ hz).hom a := by
    intro w hw e
    subst hw
    rfl
  have k2 : ((l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appLE U ⊤
      (hl ▸ hz)).hom a = 0 := by
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  rw [tr _ hl, k1] at k2
  have h1 : q a = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).hom.hom k2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem loc_div {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, hU, g, rfl⟩ := P.presheaf.exists_germ_eq t
  have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
  have e : gs (𝟙 P) x (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) x (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := by
    rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_constFn p' _ _ x hm, Category.id_comp, ht,
      gs_eq _ x U hU]
    rfl
  rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
  obtain ⟨U', hU', i₁, i₂, e'⟩ := P.presheaf.germ_eq x hm hm _ _ e
  have le : U' ≤ W ⊓ U := i₁.le
  refine ⟨U', le.trans inf_le_left, hU', (P.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom g, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 P) y U') e'
  have k := (gs_res (𝟙 P) y le hy _).symm.trans (e''.trans (gs_res (𝟙 P) y le hy _))
  have hy' : (𝟙 P : P ⟶ P) y ∈ W ⊓ U := le hy
  have k' : gs (𝟙 P) y (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) y (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := k
  rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_constFn p' _ _ y hy', Category.id_comp] at k'
  rw [k', gs_res _ y _ hy]

theorem dvd_germ_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r ∣
      gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a := by
  let P := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  let f : P ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of V) J
  have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have h' : cst (f ≫ p) x' r ∣ gs (𝟙 P) x' (f ⁻¹ᵁ W) ((f.app W).hom a) := by
    rw [gs_pull (𝟙 P) f x' W hx, Category.id_comp]; exact h
  obtain ⟨U', hU'W, hxU', t', ht'⟩ := loc_div (f ≫ p) (f ⁻¹ᵁ W) ((f.app W).hom a) r x' hx h'
  obtain ⟨O, hO, hOeq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.1 U'.isOpen
  have hxO : f x' ∈ O := by
    have : x' ∈ f.base ⁻¹' O := by rw [hOeq]; exact hxU'
    exact this
  obtain ⟨U, hU, hxU, hUsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
    (show f x' ∈ (⟨O, hO⟩ ⊓ W : X.Opens) from ⟨hxO, hx⟩)
  have hUW : U ≤ W := hUsub.trans inf_le_right
  have hfU : f ⁻¹ᵁ U ≤ U' := fun y hy => by
    have hyO : f y ∈ O := (hUsub hy).1
    have : y ∈ f.base ⁻¹' O := hyO
    rw [hOeq] at this
    exact this
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective f U hU ((P.presheaf.map (homOfLE hfU).op).hom t')
  have hd : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a) = (f.app U).hom (constFn p U r * b) := by
    apply fn_ext
    intro y hy
    have hyW : f y ∈ W := hUW hy
    have L1 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy ((X.presheaf.map (homOfLE hUW).op).hom a)
      rw [Category.id_comp, gs_res f y hUW hy] at e1
      have e2 := gs_pull (𝟙 P) f y W hyW a
      rw [Category.id_comp] at e2
      rw [e1, ← e2]
      exact ht' y (hfU hy)
    have L2 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom (constFn p U r * b)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy (constFn p U r * b)
      rw [Category.id_comp, gs_mul f y U hy, gs_constFn p U f y hy] at e1
      have e3 := gs_pull (𝟙 P) f y U hy b
      rw [Category.id_comp, hb, gs_res (𝟙 P) y hfU hy] at e3
      rw [e1, e3]
    exact L1.trans L2.symm
  have hd0 : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hmem := mem_map_of_app_fst_eq_zero p J hU _ hd0
  have hle : J.map (strMap p U) ≤ Ideal.span {strMap p U r} := by
    refine (Ideal.map_mono hJ).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hle hmem)
  have ha : (X.presheaf.map (homOfLE hUW).op).hom a = constFn p U r * (b + c) := by
    rw [mul_add, ← constFn_eq_strMap] at *
    linear_combination -hc
  refine ⟨gs (𝟙 X) (f x') U (b + c), ?_⟩
  rw [← gs_res (𝟙 X) (f x') hUW hxU, ha, gs_mul (𝟙 X) (f x') U hxU, gs_constFn p U (𝟙 X) (f x') hxU, Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.DVR
