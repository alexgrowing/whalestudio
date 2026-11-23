import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

theorem isUnit_ev_of_le (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : ⊤ ≤ z ⁻¹ᵁ Z.basicOpen a) : IsUnit (ev z U h a) := by
  rw [← ev_res z (Z.basicOpen_le a) hu h]
  exact (Z.toRingedSpace.isUnit_res_basicOpen a).map _

theorem residue_le {U : Z.Opens} {x : Z} (hx : x ∈ U) :
    ⊤ ≤ (Z.fromSpecResidueField x : Sp (Z.residueField x) ⟶ Z) ⁻¹ᵁ U := fun p _ => by
  show Z.fromSpecResidueField x p ∈ U
  rwa [Scheme.fromSpecResidueField_apply]

theorem eq_zero_of_dense [IsReduced Z] {Ω : Set Z} (hΩ : Dense Ω) {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), Set.range w ⊆ Ω → ∀ h : ⊤ ≤ w ⁻¹ᵁ U, ev w U h a = 0) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot a ?_
  by_contra hne
  obtain ⟨x, hx, hxΩ⟩ := hΩ.inter_open_nonempty _ (Z.basicOpen a).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have h1 := residue_le (Z.basicOpen_le a hx)
  refine (isUnit_ev_of_le _ U h1 a (residue_le hx)).ne_zero (H _ _ ?_ h1)
  rintro _ ⟨p, rfl⟩
  exact (Scheme.fromSpecResidueField_apply x p).symm ▸ hxΩ

variable {O : Type} [CommRing O] {N : ℕ}

theorem comp_eq_pt (q : Z ⟶ PSpace O N) {U : Z.Opens} {i : Fin (N + 1)} (hi : U ≤ q ⁻¹ᵁ chart O N i)
    (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U) (g : O →+* S) (hg : (w ≫ q) ≫ PSpace.str O N = spMap g) :
    ∃ hv, w ≫ q = pt g (fun j => ev w U hw (pullRatio q U i hi j)) hv := by
  have h1 : ev w U hw (pullRatio q U i hi i) = 1 := by rw [pullRatio_self, map_one]
  have hv : Ideal.span (Set.range fun j => ev w U hw (pullRatio q U i hi j)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by simp only [h1, isUnit_one])
  refine ⟨hv, hom_ext (hg.trans (pt_str _ _ hv).symm) fun y => ?_⟩
  have h2 : ⊤ ≤ pt g _ hv ⁻¹ᵁ chart O N i := by
    rw [pt_preimage_chart, h1]
    exact fun p _ => mem_spOpen.2 ((Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  refine ⟨⊤, trivial, i, le_preimage_map q hi hw, h2, fun j => ?_⟩
  have h3 := pullRatio_pt_mul g _ hv i j h2
  rw [h1, map_one, _root_.mul_one, fnOn_ev, appLE_pullRatio] at h3
  exact h3.symm

theorem exists_local {Z' : Scheme.{0}} (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (Em : C.Emb N) (q : Z' ⟶ PSpace O N)
    (Ω : Set Z') (hq : q ≫ PSpace.str O N = f ≫ s) [IsReduced Z'] (hΩ : Dense Ω)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α),
      ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _),
        w ≫ q = pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) (x : Z') :
    ∃ (B : Z'.Opens) (_ : IsAffineOpen B) (_ : x ∈ B) (α : C.A) (le : B ≤ f ⁻¹ᵁ C.B α) (η : Fin (C.n α) → Γ(Z', B)),
      (∃ c, IsUnit (η c)) ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ B) (g : O →+* K),
        w ≫ f ≫ s = spMap g → ∃ hv, w ≫ q = pt g (((Em.A α).map (ev (w ≫ f) _ (le_preimage_map f le hw))).mulVec
          fun i => ev w _ hw (η i)) hv := by
  obtain ⟨α, hα⟩ := C.cover (f x)
  obtain ⟨i, hi⟩ := exists_mem_chart O N (q x)
  obtain ⟨A', hA'⟩ := Em.linv α
  let U : Z'.Opens := f ⁻¹ᵁ C.B α ⊓ q ⁻¹ᵁ chart O N i
  have hxU : x ∈ U := ⟨hα, hi⟩
  let φ : Γ(Z, C.B α) →+* Γ(Z', U) := (f.appLE (C.B α) U inf_le_left).hom
  let ξ : Fin (N + 1) → Γ(Z', U) := pullRatio q U i inf_le_right
  let η : Fin (C.n α) → Γ(Z', U) := (A'.map φ).mulVec ξ
  have hev : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) {m n : ℕ}
      (M : Matrix (Fin m) (Fin n) Γ(Z, C.B α)) (v : Fin n → Γ(Z', U)),
      (fun j => ev w U hw ((M.map φ).mulVec v j)) =
        (M.map (ev (w ≫ f) _ (le_preimage_map f inf_le_left hw))).mulVec fun j => ev w U hw (v j) := by
    intro K _ w hw m n M v
    funext j
    rw [RingHom.map_mulVec, Matrix.map_map]
    congr 2
    exact funext fun a => ev_appLE w f _ hw _ a
  have hpt : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (g : O →+* K), w ≫ f ≫ s = spMap g →
      ∃ hv, w ≫ q = pt g (fun j => ev w U hw (ξ j)) hv := fun K _ w hw g hg =>
    comp_eq_pt q inf_le_right w hw g (by rw [Category.assoc, hq, hg])
  have key : ((Em.A α).map φ).mulVec η = ξ := by
    funext j
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    obtain ⟨ξ₀, g, hv, e⟩ := H K w hwΩ α (le_preimage_map f inf_le_left hw)
    obtain ⟨hv', e'⟩ := hpt K w hw g (by rw [← hq, ← Category.assoc, e, pt_str])
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')
    rw [map_sub, sub_eq_zero]
    refine congrFun (f := fun j => ev w U hw ((((Em.A α).map φ).mulVec η) j)) (g := fun j => ev w U hw (ξ j)) ?_ j
    rw [hev, hev, hu, Units.smul_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.map_mul, hA',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Matrix.mulVec_smul]
  have hc : ∃ c, x ∈ Z'.basicOpen (η c) := by
    have hw := residue_le hxU
    by_contra! hn
    have h0 : (fun c => ev _ U hw (η c)) = 0 := funext fun c => by
      by_contra hne
      have := mem_basicOpen_of_isUnit_ev _ U hw _ (Ne.isUnit hne) (IsLocalRing.closedPoint _)
      exact hn c ((Scheme.fromSpecResidueField_apply x _) ▸ this)
    have h1 := congrFun (hev _ _ hw (Em.A α) η) i
    rw [h0, Matrix.mulVec_zero, key] at h1
    have h2 : ξ i = 1 := pullRatio_self
    simp only [h2, map_one, Pi.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hc
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hc (Z'.basicOpen (η c)).isOpen
  have hBU : B ≤ U := fun y hy => Z'.basicOpen_le _ (hle hy)
  refine ⟨B, hB, hxB, α, hBU.trans inf_le_left, fun j => resG Z' hBU (η j), ⟨c, ?_⟩, fun K _ w hw g hg => ?_⟩
  · refine isUnit_of_basicOpen_eq _ ((Scheme.basicOpen_res _ _ _).trans (inf_eq_left.2 hle))
  · have hw' := le_preimage_mono hBU hw
    obtain ⟨hv, e⟩ := hpt K w hw' g hg
    have e1 : (fun j => ev w U hw' (ξ j)) = ((Em.A α).map (ev (w ≫ f) _ (le_preimage_map f (hBU.trans inf_le_left)
        hw))).mulVec fun i => ev w _ hw (resG Z' hBU (η i)) := by
      rw [← key, hev]
      congr 1
      exact funext fun j => (ev_res w hBU hw hw' _).symm
    exact ⟨e1 ▸ hv, e.trans (by congr 1)⟩

theorem exists_line : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (N : ℕ) (Em : C.Emb N) (q : Z' ⟶ PSpace O N) (Ω : Set Z'), q ≫ PSpace.str O N = f ≫ s → IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _), w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) → ∃ L : C.Line f, ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → K) (g : O →+* K), w ≫ f ≫ s = spMap g → (L.Carries w α h ξ ↔ ∃ hv, w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) := by
  intro O _ Z Z' s f C N Em q Ω hq hred hΩ H
  choose B aff mem a le η unit hη using exists_local s f C Em q Ω hq hΩ H
  refine ⟨⟨Z', B, aff, fun x => ⟨x, mem x⟩, a, le, η, unit⟩, fun K _ w α h ξ g hg => ⟨fun hL => ?_, ?_⟩⟩
  · have hw : ⊤ ≤ w ⁻¹ᵁ B (w (IsLocalRing.closedPoint K)) :=
      ((IsLocalRing.closed_point_mem_iff (U := w ⁻¹ᵁ B _)).1 (mem _)).ge
    generalize w (IsLocalRing.closedPoint K) = β at hw
    obtain ⟨u, hu⟩ := hL β hw
    obtain ⟨hv, e⟩ := hη β K w hw g hg
    obtain ⟨u', hu'⟩ := Em.compat (a β) α K (w ≫ f) (le_preimage_map f (le β) hw) h
    have hu1 : (C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ =
      (u : K) • fun i => ev w _ hw (η β i) := hu
    have e1 : ((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ = (u'⁻¹ * u) • ((Em.A (a β)).map
        (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec fun i => ev w _ hw (η β i) := by
      rw [mul_smul, eq_inv_smul_iff, Units.smul_def, Units.smul_def, ← Matrix.smul_mulVec, ← hu',
        ← Matrix.mulVec_mulVec, hu1, Matrix.mulVec_smul]
    have hv' := e1 ▸ span_range_units_smul hv (u'⁻¹ * u)
    exact ⟨hv', e.trans ((pt_eq_pt_iff g hv hv').2 ⟨_, e1⟩)⟩
  · rintro ⟨hv', e'⟩ β hw
    obtain ⟨hv, e⟩ := hη β K w hw g hg
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')
    obtain ⟨u', hu'⟩ := Em.compat (a β) α K (w ≫ f) (le_preimage_map f (le β) hw) h
    obtain ⟨A', hA'⟩ := Em.linv (a β)
    have hl : ∀ v, (A'.map (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec (((Em.A (a β)).map
        (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    refine ⟨u' * u, ?_⟩
    show (C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ =
      ((u' * u : Kˣ) : K) • fun i => ev w _ hw (η β i)
    rw [← hl ((C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ), Matrix.mulVec_mulVec ξ, hu',
      Matrix.smul_mulVec, hu, Units.smul_def, smul_smul, Matrix.mulVec_smul, hl, Units.val_mul]

end GlobalTheory.DRFlag.LineOfMap
