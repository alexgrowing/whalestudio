import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.LocM.Recode

section Sch

variable {X' X : Scheme.{0}} {f : X' ⟶ X} {U : X.Opens} {j : U.toScheme ⟶ X'}

theorem exists_lift (hp : IsPullback j (𝟙 U.toScheme) f U.ι) {T : Scheme.{0}} (w : T ⟶ X')
    (hw : Set.range (w ≫ f) ⊆ (U : Set X)) : ∃ w₀ : T ⟶ U.toScheme, w₀ ≫ j = w ∧ w₀ ≫ U.ι = w ≫ f := by
  have h : Set.range (w ≫ f) ⊆ Set.range U.ι := by simpa using hw
  let v := IsOpenImmersion.lift U.ι (w ≫ f) h
  have hv : v ≫ U.ι = w ≫ f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨hp.lift w v hv.symm, hp.lift_fst _ _ _, ?_⟩
  have := hp.lift_snd w v hv.symm
  rw [Category.comp_id] at this
  rw [this, hv]

theorem lift_unique (hp : IsPullback j (𝟙 U.toScheme) f U.ι) {T : Scheme.{0}} (w w' : T ⟶ X')
    (hw : Set.range (w ≫ f) ⊆ (U : Set X)) (h : w ≫ f = w' ≫ f) : w = w' := by
  obtain ⟨a, ha, ha'⟩ := exists_lift hp w hw
  obtain ⟨b, hb, hb'⟩ := exists_lift hp w' (h ▸ hw)
  have : a = b := by rw [← cancel_mono U.ι, ha', hb', h]
  rw [← ha, ← hb, this]

theorem exists_lift' (hp : IsPullback j (𝟙 U.toScheme) f U.ι) {T : Scheme.{0}} (v : T ⟶ X)
    (hv : Set.range v ⊆ (U : Set X)) : ∃ w : T ⟶ X', w ≫ f = v := by
  have h : Set.range v ⊆ Set.range U.ι := by simpa using hv
  refine ⟨IsOpenImmersion.lift U.ι v h ≫ j, ?_⟩
  rw [Category.assoc, hp.w, Category.id_comp, IsOpenImmersion.lift_fac]

theorem isIso_res (hp : IsPullback j (𝟙 U.toScheme) f U.ι) : IsIso (f ∣_ U) := by
  have h := isPullback_morphismRestrict f U
  have : f ∣_ U = (h.isoIsPullback _ _ hp.flip).hom := by
    have := h.isoIsPullback_hom_fst _ _ hp.flip
    simpa using this.symm
  rw [this]; infer_instance

theorem isIso_res_le (hp : IsPullback j (𝟙 U.toScheme) f U.ι) (V : X.Opens) (hV : V ≤ U) : IsIso (f ∣_ V) := by
  have := isIso_res hp
  have h1 : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  have h2 : IsIso (f ∣_ (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).1 h1
  have h3 : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hV
  rwa [h3] at h2

theorem range_j_subset (hp : IsPullback j (𝟙 U.toScheme) f U.ι) : Set.range j ⊆ f ⁻¹' (U : Set X) := by
  rintro _ ⟨x, rfl⟩
  have h : f (j x) = U.ι x := by
    rw [← Scheme.Hom.comp_apply, hp.w, Category.id_comp]
  change f (j x) ∈ (U : Set X)
  rw [h]
  exact x.2

theorem isAffineOpen_pre (hp : IsPullback j (𝟙 U.toScheme) f U.ι) {V : X.Opens} (hV : IsAffineOpen V) (hU : V ≤ U) :
    IsAffineOpen (f ⁻¹ᵁ V) := by
  have := isIso_res_le hp V hU
  have : IsAffine V.toScheme := hV
  exact IsAffine.of_isIso (f ∣_ V)

theorem exists_chart_iso (hp : IsPullback j (𝟙 U.toScheme) f U.ι) {V : X.Opens} (hV : IsAffineOpen V) (hU : V ≤ U) :
    ∃ ρ : Γ(X, V) ≃+* Γ(X', f ⁻¹ᵁ V), spMap ρ.toRingHom ≫ hV.fromSpec = (isAffineOpen_pre hp hV hU).fromSpec ≫ f := by
  have := isIso_res_le hp V hU
  let hV' := isAffineOpen_pre hp hV hU
  let g : Spec Γ(X', f ⁻¹ᵁ V) ⟶ Spec Γ(X, V) := hV'.isoSpec.inv ≫ f ∣_ V ≫ hV.isoSpec.hom
  have hg : Spec.map (Spec.preimage g) = g := Spec.map_preimage g
  have hi : IsIso (Spec.map (Spec.preimage g)) := by rw [hg]; infer_instance
  have hi' : IsIso (Spec.preimage g) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage g).op) := hi
    have := isIso_of_reflects_iso (Spec.preimage g).op Scheme.Spec
    exact isIso_of_op _
  refine ⟨(asIso (Spec.preimage g)).commRingCatIsoToRingEquiv, ?_⟩
  change Spec.map (Spec.preimage g) ≫ _ = _
  rw [hg, ← hV.isoSpec_inv_ι, ← hV'.isoSpec_inv_ι]
  simp only [g, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

end Sch

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : A →+* B) (q : B →+* C) :
    spMap q ≫ spMap p = spMap (q.comp p) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : A →+* B) (q : B →+* C) :
    (dualMap q).comp (dualMap p) = dualMap (q.comp p) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem bc_bc {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : A →+* B) (q : B →+* C)
    (u : Vecs Dw t A) : (u.bc p).bc q = u.bc (q.comp p) := by
  funext τ i
  simp only [Vecs.bc]
  rw [← Category.assoc, spMap_comp_eq, dualMap_comp_eq]

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem chart_le (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : (U : Set Z.X) = Z.opn) (a : Fin Z.m) : (Z.U a).1 ≤ U := by
  intro x hx
  change x ∈ (U : Set Z.X)
  rw [hU, ← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, hx⟩

theorem range_chart (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : (U : Set Z.X) = Z.opn) (a : Fin Z.m) {T : Scheme.{0}}
    (v : T ⟶ Sp Γ(Z.X, (Z.U a).1)) : Set.range (v ≫ Z.chart a) ⊆ (U : Set Z.X) := by
  rintro _ ⟨x, rfl⟩
  apply chart_le Z hU a
  have : (Z.U a).2.fromSpec (v x) ∈ Set.range (Z.U a).2.fromSpec := ⟨_, rfl⟩
  exact (IsAffineOpen.range_fromSpec (Z.U a).2).le this

section Core

variable (Z : Mdl Y i₀) {n : ℕ} (I : (PSpace (Z.i.c.V W) n).IdealSheafData) (f : I.subscheme ⟶ Z.X) {U : Z.X.Opens}
  {j : U.toScheme ⟶ I.subscheme} (hU : (U : Set Z.X) = Z.opn) (hp : IsPullback j (𝟙 U.toScheme) f U.ι)

def rho (a : Fin Z.m) : Γ(Z.X, (Z.U a).1) ≃+* Γ(I.subscheme, f ⁻¹ᵁ (Z.U a).1) :=
  (exists_chart_iso hp (Z.U a).2 (chart_le Z hU a)).choose

def pre : Pre Y i₀ where
  i := Z.i
  dvd := Z.dvd
  le := Z.le
  n := n
  I := I
  π := f ≫ Z.π
  ty := Z.ty
  m := Z.m
  U a := ⟨f ⁻¹ᵁ (Z.U a).1, isAffineOpen_pre hp (Z.U a).2 (chart_le Z hU a)⟩
  alg a := (rho Z I f hU hp a).toRingHom.comp (Z.alg a)
  fr a := (Z.fr a).bc (rho Z I f hU hp a).toRingHom

def ch (a : Fin Z.m) : Sp Γ(I.subscheme, f ⁻¹ᵁ (Z.U a).1) ⟶ I.subscheme :=
  (isAffineOpen_pre hp (Z.U a).2 (chart_le Z hU a)).fromSpec

theorem chart_comp (a : Fin Z.m) :
    ch Z I f hU hp a ≫ f = spMap (rho Z I f hU hp a).toRingHom ≫ Z.chart a :=
  (exists_chart_iso hp (Z.U a).2 (chart_le Z hU a)).choose_spec.symm

theorem flagAt_iff {k : Type} [Field k] (w : Sp k ⟶ I.subscheme) (u : Vecs Dw (Y Z.i).t k) :
    (pre Z I f hU hp).FlagAt w u ↔ Z.FlagAt (w ≫ f) u := by
  change (∃ (a : Fin Z.m) (φ : Γ(I.subscheme, f ⁻¹ᵁ (Z.U a).1) →+* k), spMap φ ≫ ch Z I f hU hp a = w ∧
    IsFrame (Y Z.i).t (φ.comp ((rho Z I f hU hp a).toRingHom.comp (Z.alg a))) (w ≫ f ≫ Z.π) u ∧
    SameFlag Z.ty (Y Z.i).t (w ≫ f ≫ Z.π) (((Z.fr a).bc (rho Z I f hU hp a).toRingHom).bc φ) u) ↔ _
  constructor
  · rintro ⟨a, φ, h1, h2, h3⟩
    refine ⟨a, RingHom.comp φ (rho Z I f hU hp a).toRingHom, ?_, ?_, ?_⟩
    · rw [← spMap_comp_eq, Category.assoc, ← chart_comp, ← h1, Category.assoc]
    · rw [Category.assoc]
      exact h2
    · rw [Category.assoc, ← bc_bc]
      exact h3
  · rintro ⟨a, φ, h1, h2, h3⟩
    have hφ : (φ.comp (rho Z I f hU hp a).symm.toRingHom).comp (rho Z I f hU hp a).toRingHom = φ := by
      ext x; simp
    refine ⟨a, φ.comp (rho Z I f hU hp a).symm.toRingHom, ?_, ?_, ?_⟩
    · have h : (spMap (φ.comp (rho Z I f hU hp a).symm.toRingHom) ≫ ch Z I f hU hp a) ≫ f = w ≫ f := by
        rw [Category.assoc, chart_comp, ← Category.assoc, spMap_comp_eq, hφ, h1]
      refine lift_unique hp _ _ ?_ h
      rw [h, ← h1]
      exact range_chart Z hU a _
    · rw [← RingHom.comp_assoc, hφ, ← Category.assoc]
      exact h2
    · rw [bc_bc, hφ, ← Category.assoc]
      exact h3

theorem opn_eq : (pre Z I f hU hp).opn = f ⁻¹' (U : Set Z.X) := by
  rw [hU]
  ext x
  exact Iff.rfl

def mdl (hs : f ≫ Z.s = I.subschemeι ≫ PSpace.str _ n) (hn : IsNormalScheme I.subscheme) (hf : Flat (f ≫ Z.s))
    (hd : Dense (Set.range j)) : Mdl Y i₀ where
  toPre := pre Z I f hU hp
  π_s := by
    change (f ≫ Z.π) ≫ (Y Z.i).s = I.subschemeι ≫ PSpace.str _ n
    rw [Category.assoc, Z.π_s, hs]
  normal := hn
  flat := by
    change Flat (I.subschemeι ≫ PSpace.str _ n)
    rw [← hs]; exact hf
  dense := by
    rw [opn_eq]
    exact hd.mono (range_j_subset hp)
  cover := by
    rw [opn_eq]
    change ⋃ a : Fin Z.m, f ⁻¹' ((Z.U a).1 : Set Z.X) = f ⁻¹' (U : Set Z.X)
    rw [hU, ← Z.cover, Set.preimage_iUnion]
  alg_s a := by
    revert a
    change ∀ a : Fin Z.m, ch Z I f hU hp a ≫ I.subschemeι ≫ PSpace.str _ n =
      spMap (((rho Z I f hU hp a).toRingHom.comp (Z.alg a)).comp (Z.i.c.V W).subtype)
    intro a
    rw [← hs, ← Category.assoc, chart_comp, Category.assoc, Z.alg_s, spMap_comp_eq, RingHom.comp_assoc]
  smooth a := by
    revert a
    change ∀ a : Fin Z.m, Smooth (ch Z I f hU hp a ≫ f ≫ Z.π)
    intro a
    rw [← Category.assoc, chart_comp, Category.assoc]
    have := Z.smooth a
    have : IsIso (spMap (rho Z I f hU hp a).toRingHom) := by
      have : IsIso (CommRingCat.ofHom (rho Z I f hU hp a).toRingHom) :=
        (rho Z I f hU hp a).toCommRingCatIso.isIso_hom
      infer_instance
    infer_instance
  frame a := by
    revert a
    change ∀ a : Fin Z.m, IsFrame (Y Z.i).t ((rho Z I f hU hp a).toRingHom.comp (Z.alg a)) (ch Z I f hU hp a ≫ f ≫ Z.π)
      ((Z.fr a).bc (rho Z I f hU hp a).toRingHom)
    intro a
    rw [← Category.assoc, chart_comp, Category.assoc]
    exact GlobalTheory.LocM.isFrame_bc _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.frame a)
  glue k _ := by
    change ∀ (a a' : Fin Z.m) (φ : Γ(I.subscheme, f ⁻¹ᵁ (Z.U a).1) →+* k) (φ' : Γ(I.subscheme, f ⁻¹ᵁ (Z.U a').1) →+* k),
      spMap φ ≫ ch Z I f hU hp a = spMap φ' ≫ ch Z I f hU hp a' →
      SameFlag Z.ty (Y Z.i).t (spMap φ ≫ ch Z I f hU hp a ≫ f ≫ Z.π) (((Z.fr a).bc (rho Z I f hU hp a).toRingHom).bc φ)
        (((Z.fr a').bc (rho Z I f hU hp a').toRingHom).bc φ')
    intro a a' φ φ' h
    rw [bc_bc, bc_bc, ← Category.assoc (ch Z I f hU hp a), chart_comp, Category.assoc, ← Category.assoc (spMap φ),
      spMap_comp_eq]
    apply Z.glue
    rw [← spMap_comp_eq, ← spMap_comp_eq, Category.assoc, Category.assoc, ← chart_comp, ← chart_comp, ← Category.assoc, h,
      Category.assoc]
  bij k _ := by
    change ∀ (g : Z.i.c.F →+* k) (y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c), y ≫ pullback.snd _ _ = spMap g →
      ∀ u, IsFrame (Y Z.i).t g (y ≫ (Y Z.i).j) u → ∃! w : Sp k ⟶ I.subscheme, w ≫ f ≫ Z.π = y ≫ (Y Z.i).j ∧
        (pre Z I f hU hp).FlagAt w u
    intro g y hy u hu
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := Z.bij k g y hy u hu
    have hr : Set.range w ⊆ (U : Set Z.X) := by
      obtain ⟨a, φ, h, -⟩ := hw2
      rw [← h]
      exact range_chart Z hU a _
    obtain ⟨w', hw'⟩ := exists_lift' hp w hr
    refine ⟨w', ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, hw', hw1]
    · rw [flagAt_iff, hw']; exact hw2
    · rintro w'' ⟨h1, h2⟩
      have h3 : w'' ≫ f = w := hw3 _ ⟨by rw [Category.assoc, h1], (flagAt_iff Z I f hU hp _ _).1 h2⟩
      exact lift_unique hp _ _ (h3 ▸ hr) (h3.trans hw'.symm)

theorem isMap_mdl (hs : f ≫ Z.s = I.subschemeι ≫ PSpace.str _ n) (hn : IsNormalScheme I.subscheme) (hf : Flat (f ≫ Z.s))
    (hd : Dense (Set.range j)) (Z₂ : Mdl Y i₀) (f₂ : I.subscheme ⟶ Z₂.X) (hc : Corr Z Z₂)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ U.toScheme), NatImg Z Z₂ (w ≫ U.ι) (w ≫ j ≫ f₂)) :
    IsMap (mdl Z I f hU hp hs hn hf hd) Z₂ f₂ := by
  refine ⟨hc, ?_⟩
  intro k _
  change ∀ w : Sp k ⟶ I.subscheme, Set.range w ⊆ (pre Z I f hU hp).opn →
    ∃ (τ : (Y Z.i).X ⟶ (Y Z₂.i).X) (mu : SABMap (Y Z.i).t (Y Z₂.i).t τ) (u : Vecs Dw (Y Z.i).t k),
    IsTrans Z₂.i Z.i τ mu ∧ (w ≫ f₂) ≫ Z₂.π = w ≫ (f ≫ Z.π) ≫ τ ∧ (pre Z I f hU hp).FlagAt w u ∧
      Z₂.FlagAt (w ≫ f₂) (fun σ i => u σ i ≫ mu.φ)
  intro w hw
  rw [opn_eq] at hw
  have hw' : Set.range (w ≫ f) ⊆ (U : Set Z.X) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw ⟨x, rfl⟩
  obtain ⟨w₀, h1, h2⟩ := exists_lift hp w hw'
  obtain ⟨τ, mu, u, t1, t2, t3, t4⟩ := h k w₀
  rw [← Category.assoc w₀ j, h1] at t2 t4
  rw [h2] at t2 t3
  refine ⟨τ, mu, u, t1, ?_, (flagAt_iff Z I f hU hp _ _).2 t3, t4⟩
  rw [t2]; simp only [Category.assoc]

end Core

theorem exists_model_of_modification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (U : Z.X.Opens) (j : U.toScheme ⟶ X'), (U : Set Z.X) = Z.opn → IsProjOver (f ≫ Z.s) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → Flat (f ≫ Z.s) → IsPullback j (𝟙 U.toScheme) f U.ι → Dense (Set.range j) → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X'), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ ∀ (Z₂ : Mdl Y i₀) (f₂ : X' ⟶ Z₂.X), GlobalTheory.LocM.Corr Z Z₂ → (∀ (k : Type) [Field k] (w : Sp k ⟶ U.toScheme), NatImg Z Z₂ (w ≫ U.ι) (w ≫ j ≫ f₂)) → IsMap Z' Z₂ (e.hom ≫ f₂) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X' f U j hU ⟨n, i, hi, hs⟩ hn hf hp hd
  have hiso : IsIso i.toImage := inferInstance
  let e : i.ker.subscheme ≅ X' := (asIso i.toImage).symm
  have he : e.inv ≫ i.ker.subschemeι = i := i.toImage_imageι
  have hp' : IsPullback (j ≫ e.inv) (𝟙 U.toScheme) (e.hom ≫ f) U.ι :=
    hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have hs' : (e.hom ≫ f) ≫ Z.s = i.ker.subschemeι ≫ PSpace.str _ n := by
    rw [Category.assoc, ← hs, ← Category.assoc]
    congr 1
    exact ((Iso.inv_comp_eq e).1 he).symm
  have hn₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme i.ker.subscheme := by
    intro x
    obtain ⟨h1, h2⟩ := hn (e.hom x)
    let φ := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨φ.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv φ⟩
  have hn' : GlobalTheory.IsNormalScheme i.ker.subscheme := ⟨fun x => (hn₀ x).1, fun x => (hn₀ x).2⟩
  have hf' : Flat ((e.hom ≫ f) ≫ Z.s) := by rw [Category.assoc]; infer_instance
  have hd' : Dense (Set.range (j ≫ e.inv)) := by
    have : DenseRange e.inv := e.inv.surjective.denseRange
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact this.comp hd e.inv.continuous
  refine ⟨mdl Z i.ker (e.hom ≫ f) hU hp' hs' hn' hf' hd', e, rfl, rfl, fun Z₂ f₂ hc h => ?_⟩
  refine isMap_mdl Z i.ker (e.hom ≫ f) hU hp' hs' hn' hf' hd' Z₂ (e.hom ≫ f₂) hc fun k _ w => ?_
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h k w

end GlobalTheory.LocM.Recode
