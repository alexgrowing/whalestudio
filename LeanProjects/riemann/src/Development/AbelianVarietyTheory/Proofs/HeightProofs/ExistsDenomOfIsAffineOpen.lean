import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

namespace GlobalTheory.SecSpread

theorem exists_denom_of_isPushout {R : Type} [CommRing R] [IsDomain R] {R₀ A K P : CommRingCat.{0}} {α : R₀ ⟶ A}
    {ψ : R₀ ⟶ K} {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout α ψ inl inr) (c : R →+* R₀)
    (hK : ∀ k : K, ∃ d : R, d ≠ 0 ∧ ∃ r : R₀, ψ.hom (c d) * k = ψ.hom r) (t : P) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : A, inl.hom (α.hom (c d)) * t = inl.hom a := by
  have hw : ∀ r, inl.hom (α.hom r) = inr.hom (ψ.hom r) := fun r => congr($(H.w).hom r)
  have ht : t ∈ Subring.closure (Set.range inl ∪ Set.range inr) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout H]; trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨1, one_ne_zero, a, by simp⟩
    · obtain ⟨d, hd, r, hr⟩ := hK k
      refine ⟨d, hd, α.hom r, ?_⟩
      rw [hw, hw, ← hr, map_mul]
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | one => exact ⟨1, one_ne_zero, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, a, ha⟩ := hx
    obtain ⟨e, he, b, hb⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, α.hom (c e) * a + α.hom (c d) * b, ?_⟩
    simp only [map_mul, map_add]
    rw [← ha, ← hb]; ring
  | neg x _ hx =>
    obtain ⟨d, hd, a, ha⟩ := hx
    exact ⟨d, hd, -a, by rw [map_neg, ← ha, mul_neg]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, a, ha⟩ := hx
    obtain ⟨e, he, b, hb⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, a * b, ?_⟩
    simp only [map_mul]
    rw [← ha, ← hb]; ring

theorem spMap_appTop {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (a : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (f a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}

theorem exists_denom_of_isAffineOpen (H : IsPullback φ π p (spMap (algebraMap R K))) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(X', φ ⁻¹ᵁ U)) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : Γ(X, U), (φ.app U).hom (constFn p U d) * t = (φ.app U).hom a := by
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := φ ⁻¹ᵁ U) (ProperFunctions.le_preimage_top _ ⊤) (ProperFunctions.le_preimage_top p U) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h := (isIso_pushoutSection_iff ..).mp this
  rw [ProperFunctions.appLE_top_top, Scheme.Hom.appLE_eq_app] at h
  refine exists_denom_of_isPushout h (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (fun k => ?_) t
  obtain ⟨k, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 k
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b, hb0, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a, ?_⟩
  rw [spMap_appTop, spMap_appTop, ← map_mul]
  congr 1
  exact mul_div_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0)

theorem ext_generic (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] {W : X.Opens} {a b : Γ(X, W)}
    (h : ∀ z, φ z ∈ W → gs φ z W a = gs φ z W b) : a = b := by
  have hf : Function.Injective (spMap (algebraMap R K)).appTop.hom := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 y
    have := ((spMap_appTop _ x).symm.trans hxy).trans (spMap_appTop _ y)
    rw [IsFractionRing.injective R K
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 this)]
  refine fn_ext fun x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hle : U ≤ W := hUW
  have e : (φ.app U).hom (resG X hle a) = (φ.app U).hom (resG X hle b) := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 X') φ z U hz' _).symm)
    rw [Category.id_comp, gs_res φ z hle hz', gs_res φ z hle hz', h z (hle hz')]
  have h0 := ProperFunctions.mem_map_ker_of_app_eq_zero H hU (resG X hle a - resG X hle b)
    ((map_sub _ _ _).trans (sub_eq_zero.2 e))
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hf, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at h0
  exact (gs_res (𝟙 X) x hle hxU a).symm.trans ((congrArg _ h0).trans (gs_res (𝟙 X) x hle hxU b))

theorem exists_glue (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] (W : X.Opens)
    (t : ∀ z : X', X'.presheaf.stalk z)
    (h : ∀ x ∈ W, ∃ (U : X.Opens) (_ : U ≤ W) (_ : x ∈ U) (a : Γ(X, U)), ∀ z, φ z ∈ U → gs φ z U a = t z) :
    ∃ θ : Γ(X, W), ∀ z, φ z ∈ W → gs φ z W θ = t z := by
  choose U hU hx a ha using fun x : W => h x.1 x.2
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U W (fun i => homOfLE (hU i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) a (fun i j => ext_generic H (W := U i ⊓ U j) fun z hz =>
      (gs_res φ z inf_le_left hz _).trans (((ha i z hz.1).trans (ha j z hz.2).symm).trans
        (gs_res φ z inf_le_right hz _).symm))
  refine ⟨s, fun z hz => ?_⟩
  exact (gs_res φ z (hU ⟨_, hz⟩) (hx _) s).symm.trans
    ((congrArg (gs φ z _) (hs ⟨_, hz⟩)).trans (ha _ z (hx _)))

omit [IsDomain R] in

theorem cst_mul {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) : cst q z (a * b) = cst q z a * cst q z b := by
  rw [cst, map_mul, gs_mul q z ⊤ trivial]; rfl

theorem isUnit_cst (hw : φ ≫ p = π ≫ spMap (algebraMap R K)) (z : X') {d : R} (hd : d ≠ 0) :
    IsUnit (cst (φ ≫ p) z d) := by
  have hu : IsUnit (algebraMap R K d) := ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd).isUnit
  rw [hw, cst, ← gs_pull π _ z ⊤ trivial]
  have e := congrArg (gs π z ⊤) (spMap_appTop (algebraMap R K) d)
  refine (congrArg IsUnit e).mpr ?_
  rw [gs_eq π z ⊤ trivial]
  exact ((hu.map _).map _).map _

theorem pull_sec_trans {L : LB X} (s : (L.pull φ).Sec) (z : X') {i j : L.ι} (hi : φ z ∈ L.U i) (hj : φ z ∈ L.U j) :
    gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) =
      (gm φ z _ (L.g i j)).val * gs (𝟙 X') z ((L.pull φ).U (fun _ => j)) (s.f (fun _ => j)) := by
  have := sec_trans s (𝟙 X') z (j := fun _ => i) (j' := fun _ => j) (mem_pull.2 hi) (mem_pull.2 hj)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp] at this
  exact this

theorem exists_spread (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] [QuasiCompact p] {L : LB X}
    (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ d : R, d ≠ 0 ∧ ∃ θ : L.Sec, ∀ i z, φ z ∈ L.U i →
      gs φ z (L.U i) (θ.f i) = cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
  classical
  have loc : ∀ x : X, ∃ (V : X.Opens) (i : L.ι) (_ : V ≤ L.U i) (_ : x ∈ V) (d : R) (_ : d ≠ 0) (a : Γ(X, V)),
      ∀ z, φ z ∈ V → gs φ z V a =
        cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    have hle : U ≤ L.U i := hUW
    have hle' : φ ⁻¹ᵁ U ≤ (L.pull φ).U (fun _ => i) := fun z hz => mem_pull.2 (hle hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom_of_isAffineOpen H hU (resG X' hle' (s.f (fun _ => i)))
    refine ⟨U, i, hle, hxU, d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ U := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z U hz, gs_pull (𝟙 X') φ z U hz,
      Category.id_comp, gs_constFn p U φ z hz] at e
    exact e.symm
  choose V ι hV hx d hd a ha using loc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  have hglue : ∀ i, ∃ θ : Γ(X, L.U i), ∀ z, φ z ∈ L.U i → gs φ z (L.U i) θ =
      cst (φ ≫ p) z (∏ x ∈ S, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
    intro i
    refine exists_glue H (L.U i) _ fun y hy => ?_
    obtain ⟨x, hxS, hyx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
    have l : L.U i ⊓ V x ≤ L.U i ⊓ L.U (ι x) := inf_le_inf_left _ (hV x)
    refine ⟨L.U i ⊓ V x, inf_le_left, ⟨hy, hyx⟩,
      constFn p _ (∏ w ∈ S.erase x, d w) * (resG X l (L.g i (ι x)).val * resG X inf_le_right (a x)), fun z hz => ?_⟩
    rw [gs_mul φ z _ hz, gs_mul φ z _ hz, gs_constFn p _ φ z hz, gs_res φ z l hz, gs_res φ z inf_le_right hz,
      ha x z hz.2, gs_unit φ z _ (l hz), pull_sec_trans s z hz.1 (hV x hz.2), ← Finset.mul_prod_erase S d hxS,
      cst_mul]
    ring
  choose θ hθ using hglue
  refine ⟨∏ x ∈ S, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, ⟨θ, fun i j => ext_generic H fun z hz => ?_⟩, hθ⟩
  rw [gs_mul φ z _ hz, gs_res φ z inf_le_left hz, gs_res φ z inf_le_right hz, gs_unit φ z _ hz, hθ i z hz.1,
    hθ j z hz.2, pull_sec_trans s z hz.1 hz.2]
  ring

theorem res_mem_secOn {L : LB X} (θ : L.Sec) (V : X.Opens) :
    (fun i => resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (θ.f i)) ∈ secOn L V := by
  intro i j
  refine fn_ext fun x hx => ?_
  have hx' : (𝟙 X : X ⟶ X) x ∈ V ⊓ L.U i ⊓ L.U j := hx
  have hm : (𝟙 X : X ⟶ X) x ∈ L.U i ⊓ L.U j := ⟨hx.1.2, hx.2⟩
  have e := congrArg (gs (𝟙 X) x _) (θ.compat i j)
  rw [gs_mul _ x _ hm, gs_res _ x _ hm, gs_res _ x _ hm] at e
  rw [gs_mul _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx'.1,
    gs_res _ x (V := V ⊓ L.U j) _ ⟨hx.1.1, hx.2⟩]
  exact e

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left), L.IsLB → ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G' : Scheme.{0}) (φ : G' ⟶ G.left) (π : G' ⟶ Sp K), IsPullback φ π G.hom (spMap (algebraMap R K)) → (∃ (s : (L.pull φ).Sec) (j : (L.pull φ).ι), s.f j ≠ 0) → ∃ h : R, h ≠ 0 ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h), ∀ y : Sp R, y ∈ PrimeSpectrum.basicOpen h → ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  intro R _ _ G _ hG L hL K _ _ _ G' φ π H ⟨s, j, hj⟩
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨d, hd, θ, hθ⟩ := exists_spread H hL s
  have : Smooth π := MorphismProperty.of_isPullback H hG.smooth
  have : IsReduced G' := isReduced_scheme_of_smooth_of_isIntegrallyClosed K π
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j PUnit.unit, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∈ G'.basicOpen (s.f (fun _ => i)) := by
    by_contra hn
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim))
  have hz₁ : z ∈ (L.pull φ).U (fun _ => i) := G'.basicOpen_le _ hz
  have hz₂ : φ z ∈ L.U i := mem_pull.1 hz₁
  have hu : IsUnit (gs φ z (L.U i) (θ.f i)) := by
    rw [hθ i z hz₂]
    refine (isUnit_cst H.w z hd).mul ?_
    rw [gs_eq (𝟙 G') z _ hz₁]
    exact (G'.mem_basicOpen _ z hz₁).1 hz
  have hb : φ z ∈ G.left.basicOpen (θ.f i) := by
    rw [gs_eq φ z _ hz₂] at hu
    have := (G'.mem_basicOpen _ z (show z ∈ φ ⁻¹ᵁ L.U i from hz₂)).2 hu
    rw [← Scheme.preimage_basicOpen] at this
    exact this
  have hopen : IsOpen (G.hom '' (G.left.basicOpen (θ.f i) : Set G.left)) :=
    G.hom.isOpenMap _ (G.left.basicOpen (θ.f i)).isOpen
  obtain ⟨_, ⟨h, rfl⟩, hyh, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem G.hom hb) hopen
  refine ⟨h, ?_, _, res_mem_secOn θ _, fun y hy => ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hyh (Ideal.zero_mem _)
  · obtain ⟨g, hg, rfl⟩ := hsub hy
    refine ⟨g, i, rfl, ?_⟩
    have e := G.left.basicOpen_res (θ.f i)
      (homOfLE (inf_le_right : G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h ⊓ L.U i ≤ L.U i)).op
    exact e.ge ⟨⟨hy, G.left.basicOpen_le _ hg⟩, hg⟩

end GlobalTheory.SecSpread
