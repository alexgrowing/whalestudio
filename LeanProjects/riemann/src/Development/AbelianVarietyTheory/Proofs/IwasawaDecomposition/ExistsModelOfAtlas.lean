import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRFlag.ToMdl

theorem exists_chart_iso {X' Y : Scheme.{0}} {R : Type} [CommRing R] (χ : Sp R ⟶ Y) [IsOpenImmersion χ]
    (g : Y ⟶ X') [IsIso g] : ∃ θ : R ≃+* Γ(X', (χ ≫ g).opensRange),
      spMap θ.toRingHom ≫ χ ≫ g = (isAffineOpen_opensRange (χ ≫ g)).fromSpec := by
  let hU := isAffineOpen_opensRange (χ ≫ g)
  let k := IsOpenImmersion.isoOfRangeEq hU.fromSpec (χ ≫ g) (by rw [hU.range_fromSpec]; simp)
  have hg : Spec.map (Spec.preimage k.hom) = k.hom := Spec.map_preimage _
  have hi : IsIso (Spec.map (Spec.preimage k.hom)) := by rw [hg]; infer_instance
  have hi' : IsIso (Spec.preimage k.hom) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage k.hom).op) := hi
    have := isIso_of_reflects_iso (Spec.preimage k.hom).op Scheme.Spec
    exact isIso_of_op _
  refine ⟨(asIso (Spec.preimage k.hom)).commRingCatIsoToRingEquiv, ?_⟩
  change Spec.map (Spec.preimage k.hom) ≫ _ = _
  rw [hg]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem range_comp_inv {X X' T : Scheme.{0}} (e : X' ≅ X) (f : T ⟶ X) :
    Set.range (f ≫ e.inv) = e.hom ⁻¹' Set.range f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← Scheme.Hom.comp_apply, Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i : Idx H p}
  {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ} (A : Atlas (Y i) π ty)

def chartNum : A.ch.ι ≃ Fin (Nat.card A.ch.ι) := Finite.equivFin _

def chartOpen {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) : X'.affineOpens :=
  ⟨(A.ch.χ a ≫ e.inv).opensRange, isAffineOpen_opensRange _⟩

def chartEquiv {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) : A.ch.R a ≃+* Γ(X', (chartOpen A e a).1) :=
  (exists_chart_iso (A.ch.χ a) e.inv).choose

theorem fromSpec_hom {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) :
    (chartOpen A e a).2.fromSpec ≫ e.hom = spMap (chartEquiv A e a).toRingHom ≫ A.ch.χ a := by
  have h := congrArg (· ≫ e.hom) (exists_chart_iso (A.ch.χ a) e.inv).choose_spec
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact h.symm

variable (i₀ : Idx H p) (hl : i₀.l.Dvd i.l) (hc : i₀.c.F ≤ i.c.F) {n : ℕ} (I : (PSpace (i.c.V W) n).IdealSheafData)
  (e : I.subscheme ≅ X)

def pre : Pre Y i₀ where
  i := i
  dvd := hl
  le := hc
  n := n
  I := I
  π := e.hom ≫ π
  ty := ty
  m := Nat.card A.ch.ι
  U b := chartOpen A e ((chartNum A).symm b)
  alg b := (chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg ((chartNum A).symm b))
  fr b := (A.fr ((chartNum A).symm b)).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom

theorem pre_flagAt_iff {k : Type} [Field k] (w : Sp k ⟶ I.subscheme) (u : Vecs Dw (Y i).t k) :
    (pre A i₀ hl hc I e).FlagAt w u ↔ A.FlagAt (w ≫ e.hom) u := by
  change (∃ (b : Fin (Nat.card A.ch.ι)) (φ : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b)).1) →+* k),
      spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec = w ∧
      IsFrame (Y i).t (φ.comp ((chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg ((chartNum A).symm b)))) (w ≫ e.hom ≫ π) u ∧
      SameFlag ty (Y i).t (w ≫ e.hom ≫ π) (((A.fr ((chartNum A).symm b)).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom).bc φ) u) ↔
    ∃ (a : A.ch.ι) (φ : A.ch.R a →+* k), spMap φ ≫ A.ch.χ a = w ≫ e.hom ∧
      IsFrame (Y i).t (φ.comp (A.alg a)) ((w ≫ e.hom) ≫ π) u ∧ SameFlag ty (Y i).t ((w ≫ e.hom) ≫ π) ((A.fr a).bc φ) u
  constructor
  · rintro ⟨b, φ, h1, h2, h3⟩
    refine ⟨_, φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom, ?_, ?_, ?_⟩
    · rw [← h1, Category.assoc, fromSpec_hom, ← Category.assoc, GlobalTheory.LocM.Recode.spMap_comp_eq]
    · rw [Category.assoc, RingHom.comp_assoc]; exact h2
    · rw [Category.assoc, ← GlobalTheory.LocM.Recode.bc_bc]; exact h3
  · rintro ⟨a, φ, h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := (chartNum A).symm.surjective a
    have hφ : (φ.comp (chartEquiv A e ((chartNum A).symm b)).symm.toRingHom).comp (chartEquiv A e ((chartNum A).symm b)).toRingHom = φ := by
      ext x; simp
    refine ⟨b, φ.comp (chartEquiv A e ((chartNum A).symm b)).symm.toRingHom, ?_, ?_, ?_⟩
    · rw [← cancel_mono e.hom, Category.assoc, fromSpec_hom, ← Category.assoc, GlobalTheory.LocM.Recode.spMap_comp_eq, hφ, h1]
    · rw [← RingHom.comp_assoc, hφ, ← Category.assoc]; exact h2
    · rw [GlobalTheory.LocM.Recode.bc_bc, hφ, ← Category.assoc]; exact h3

end GlobalTheory.DRFlag.ToMdl

namespace GlobalTheory.DRFlag.ToMdl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i : Idx H p}
  {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ} (A : Atlas (Y i) π ty)
  (i₀ : Idx H p) (hl : i₀.l.Dvd i.l) (hc : i₀.c.F ≤ i.c.F) {n : ℕ} (I : (PSpace (i.c.V W) n).IdealSheafData)
  (e : I.subscheme ≅ X)

def mdl (hs : e.hom ≫ π ≫ (Y i).s = I.subschemeι ≫ PSpace.str _ n) (g : Geo (Y i) π) : Mdl Y i₀ where
  toPre := pre A i₀ hl hc I e
  π_s := by
    change (e.hom ≫ π) ≫ (Y i).s = I.subschemeι ≫ PSpace.str _ n
    rw [Category.assoc, hs]
  normal := by
    have hn₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme I.subscheme := by
      intro x
      obtain ⟨h1, h2⟩ := g.normal (e.hom x)
      let φ := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
      exact ⟨φ.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv φ⟩
    exact GlobalTheory.IsNormalScheme.of_pred hn₀
  flat := by
    change Flat (I.subschemeι ≫ PSpace.str _ n)
    rw [← hs]
    have := g.flat
    infer_instance
  dense := by
    change Dense ((e.hom ≫ π) ⁻¹' Set.range (Y i).j)
    exact g.dense.preimage (f := ⇑e.hom) e.hom.isOpenEmbedding.isOpenMap
  cover := by
    change ⋃ b, (((A.ch.χ ((chartNum A).symm b) ≫ e.inv).opensRange : I.subscheme.Opens) : Set I.subscheme) =
      (e.hom ≫ π) ⁻¹' Set.range (Y i).j
    simp only [Scheme.Hom.coe_opensRange, range_comp_inv]
    rw [(chartNum A).symm.surjective.iUnion_comp (fun a => e.hom ⁻¹' Set.range (A.ch.χ a)), ← Set.preimage_iUnion]
    change e.hom ⁻¹' A.ch.carrier = _
    rw [A.cover]
    rfl
  alg_s b := by
    change (chartOpen A e _).2.fromSpec ≫ I.subschemeι ≫ PSpace.str _ n = _
    rw [← hs, ← Category.assoc, fromSpec_hom, Category.assoc, A.alg_s, GlobalTheory.LocM.Recode.spMap_comp_eq]
    rfl
  smooth b := by
    change Smooth ((chartOpen A e _).2.fromSpec ≫ e.hom ≫ π)
    rw [← Category.assoc, fromSpec_hom, Category.assoc]
    have := A.smooth ((chartNum A).symm b)
    have : IsIso (spMap (chartEquiv A e ((chartNum A).symm b)).toRingHom) := by
      have : IsIso (CommRingCat.ofHom (chartEquiv A e ((chartNum A).symm b)).toRingHom) :=
        (chartEquiv A e ((chartNum A).symm b)).toCommRingCatIso.isIso_hom
      infer_instance
    infer_instance
  frame b := by
    change IsFrame (Y i).t ((chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg _))
      ((chartOpen A e _).2.fromSpec ≫ e.hom ≫ π) ((A.fr _).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom)
    rw [← Category.assoc, fromSpec_hom, Category.assoc]
    exact GlobalTheory.LocM.isFrame_bc _ _ _ _ _ _ _ _ _ _ _ _ _ (A.frame _)
  glue k _ := by
    change ∀ (b b' : Fin (Nat.card A.ch.ι)) (φ : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b)).1) →+* k)
      (φ' : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b')).1) →+* k),
      spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec = spMap φ' ≫ (chartOpen A e ((chartNum A).symm b')).2.fromSpec →
      SameFlag ty (Y i).t (spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec ≫ e.hom ≫ π)
        (((A.fr _).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom).bc φ) (((A.fr _).bc (chartEquiv A e ((chartNum A).symm b')).toRingHom).bc φ')
    intro b b' φ φ' h
    have h' : spMap (φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom) ≫ A.ch.χ ((chartNum A).symm b) =
        spMap (φ'.comp (chartEquiv A e ((chartNum A).symm b')).toRingHom) ≫ A.ch.χ ((chartNum A).symm b') := by
      rw [← GlobalTheory.LocM.Recode.spMap_comp_eq, ← GlobalTheory.LocM.Recode.spMap_comp_eq, Category.assoc, Category.assoc,
        ← fromSpec_hom, ← fromSpec_hom, ← Category.assoc, ← Category.assoc, h]
    have hp : spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec ≫ e.hom ≫ π =
        spMap (φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom) ≫ A.ch.χ ((chartNum A).symm b) ≫ π := by
      rw [← GlobalTheory.LocM.Recode.spMap_comp_eq]
      simp only [Category.assoc]
      rw [← Category.assoc (spMap (chartEquiv A e ((chartNum A).symm b)).toRingHom) (A.ch.χ _) π, ← fromSpec_hom]
      simp only [Category.assoc]
    rw [GlobalTheory.LocM.Recode.bc_bc, GlobalTheory.LocM.Recode.bc_bc, hp]
    exact A.glue k _ _ _ _ h'
  bij k _ := by
    change ∀ (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f →
      ∀ u, IsFrame (Y i).t f (y ≫ (Y i).j) u →
        ∃! w : Sp k ⟶ I.subscheme, w ≫ e.hom ≫ π = y ≫ (Y i).j ∧ (pre A i₀ hl hc I e).FlagAt w u
    intro f y hy u hu
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := A.bij k f y hy u hu
    refine ⟨w ≫ e.inv, ⟨?_, ?_⟩, fun w' ⟨h1, h2⟩ => ?_⟩
    · rw [Category.assoc, Iso.inv_hom_id_assoc]; exact hw1
    · refine (pre_flagAt_iff A i₀ hl hc I e _ u).2 ?_
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hw2
    · have := hw3 (w' ≫ e.hom) ⟨by rw [Category.assoc, h1], (pre_flagAt_iff A i₀ hl hc I e w' u).1 h2⟩
      rw [← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.DRFlag.ToMdl

namespace GlobalTheory.DRFlag

namespace ToMdl

theorem comp_hom_comp {X' X X₂ T Z : Scheme.{0}} (w : T ⟶ X') (e : X' ≅ X) (f : X ⟶ X₂) (π₂ : X₂ ⟶ Z) (π : X ⟶ Z)
    (hf : f ≫ π₂ = π) : (w ≫ e.hom ≫ f) ≫ π₂ = w ≫ (e.hom ≫ π) ≫ 𝟙 Z := by
  simp [hf]

theorem of_assoc {X' X X₂ T : Scheme.{0}} (w : T ⟶ X') (e : X' ≅ X) (f : X ⟶ X₂) (P : (T ⟶ X₂) → Prop)
    (h : P ((w ≫ e.hom) ≫ f)) : P (w ≫ e.hom ≫ f) := by
  rwa [Category.assoc] at h

end ToMdl

theorem exists_mdl_of_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → Geo (Y i) π → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X), Z'.i = i ∧ Z'.ty = ty ∧ (∀ (Z₁ : Mdl Y i₀) (g : Z₁.X ⟶ X), MapsTo Z₁ A g → MapsTo Z₁ (atlasOf Z') (g ≫ e.inv)) ∧ (∀ (X₂ : Scheme.{0}) (π₂ : X₂ ⟶ (Y i).X) (ty₂ : (E →+* ℂ) → Finset ℕ) (A₂ : Atlas (Y i) π₂ ty₂) (f : X ⟶ X₂), f ≫ π₂ = π → (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y i).t K), A.FlagAt w u → A₂.FlagAt (w ≫ f) u) → MapsTo Z' A₂ (e.hom ≫ f)) ∧ ∀ σ k, IntStep A σ k → IntStep (atlasOf Z') σ k := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A hl hc g
  obtain ⟨n, ι, hι, hs⟩ := g.proj
  have hiso : IsIso ι.toImage := inferInstance
  let e : ι.ker.subscheme ≅ X := (asIso ι.toImage).symm
  have he : e.inv ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have hs' : e.hom ≫ π ≫ (Y i).s = ι.ker.subschemeι ≫ PSpace.str _ n := by
    calc e.hom ≫ π ≫ (Y i).s = e.hom ≫ ι ≫ PSpace.str _ n := by rw [hs]
      _ = e.hom ≫ (e.inv ≫ ι.ker.subschemeι) ≫ PSpace.str _ n := by rw [he]
      _ = _ := by simp
  refine ⟨ToMdl.mdl A i₀ hl hc ι.ker e hs' g, e, rfl, rfl, ?_, ?_, ?_⟩
  · intro Z₁ f hf k _ w hw
    obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hf k w hw
    refine ⟨τ, mu, u, h1, ?_, h3, ?_⟩
    · have h5 : (w ≫ f ≫ e.inv) ≫ e.hom ≫ π = (w ≫ f) ≫ π := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact h5.trans h2
    · refine (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e (w ≫ f ≫ e.inv) _).2 ?_
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact h4
  · intro X₂ π₂ ty₂ A₂ f hf hfl k _ w hw
    obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) i
    have hw' : (w ≫ e.hom) (IsLocalRing.closedPoint k) ∈ A.ch.carrier := by
      rw [A.cover]
      exact hw ⟨_, rfl⟩
    obtain ⟨a, φ, ha⟩ := A.ch.exists_fac (w ≫ e.hom) hw'
    refine ⟨𝟙 _, mu, (A.fr a).bc φ, ht, ?_, ?_, ?_⟩
    · exact ToMdl.comp_hom_comp w e f π₂ π hf
    · exact (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e w _).2 (A.flagAt_fr ha)
    · have h5 : (fun σ j => (A.fr a).bc φ σ j ≫ mu.φ) = (A.fr a).bc φ := by
        funext σ j
        rw [hmu]
        exact Category.comp_id _
      exact (congrArg (A₂.FlagAt (w ≫ e.hom ≫ f)) h5).mpr
        (ToMdl.of_assoc w e f (fun v => A₂.FlagAt v ((A.fr a).bc φ)) (hfl k (w ≫ e.hom) _ (A.flagAt_fr ha)))
  · intro σ k h
    exact GlobalTheory.T.atlas_pullback_preserves_step E H Dw i.l (Xo i.l) i.c (i.c.V W) (Y i) X π ty A σ k _ e.hom ty (atlasOf (ToMdl.mdl A i₀ hl hc ι.ker e hs' g))
      (fun K _ w u hw => (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e w u).1 hw) h

end GlobalTheory.DRFlag
