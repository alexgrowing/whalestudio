import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi

theorem dvd_of_tensor {V F A : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    [CommRing A] [Algebra V A] [Module.Flat V A] {ϖ : V} (hϖ : Irreducible ϖ) (v : AddValuation F (WithTop ℚ))
    (hinj : Function.Injective (algebraMap V F)) (h0 : ∀ t, 0 ≤ v (algebraMap V F t)) (h1 : 0 < v (algebraMap V F ϖ))
    {n : ℕ} (b : Fin n → F) (hb : ∀ i, 0 < v (b i)) (a : A) (c : Fin n → A)
    (h : a ⊗ₜ[V] (1 : F) = ∑ i, c i ⊗ₜ[V] b i) : algebraMap V A ϖ ∣ a := by
  classical
  let R : Subring F :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {x y} hx hy => by
        show 0 ≤ v (x * y)
        rw [v.map_mul]
        exact add_nonneg hx hy
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {x y} hx hy => le_trans (le_min hx hy) (v.map_add x y)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]
        exact le_top
      neg_mem' := fun {x} hx => by
        show 0 ≤ v (-x)
        rw [v.map_neg]
        exact hx }
  let mI : Ideal R :=
    { carrier := {x | 0 < v (x : F)}
      add_mem' := fun {x y} hx hy => lt_of_lt_of_le (lt_min hx hy) (v.map_add _ _)
      zero_mem' := by
        show 0 < v ((0 : R) : F)
        rw [Subring.coe_zero, v.map_zero]
        exact WithTop.coe_lt_top 0
      smul_mem' := fun c x hx => by
        show 0 < v ((c : F) * (x : F))
        rw [v.map_mul]
        exact lt_of_lt_of_le hx (le_add_of_nonneg_left c.2) }
  have hm1 : (1 : R) ∉ mI := by
    show ¬ (0 < v ((1 : R) : F))
    rw [Subring.coe_one, v.map_one]
    exact lt_irrefl 0
  let iota : V →+* R := (algebraMap V F).codRestrict R h0
  letI : Algebra V R := iota.toAlgebra
  haveI hmax : (Ideal.span {ϖ} : Ideal V).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hI : ∀ t ∈ (Ideal.span {ϖ} : Ideal V), (Ideal.Quotient.mk mI).comp iota t = 0 := by
    intro t ht
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    show 0 < v (algebraMap V F (y * ϖ))
    rw [map_mul, v.map_mul]
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_left (h0 y))
  letI : Field (V ⧸ (Ideal.span {ϖ} : Ideal V)) := Ideal.Quotient.field _
  let phi : V ⧸ (Ideal.span {ϖ} : Ideal V) →+* R ⧸ mI :=
    Ideal.Quotient.lift (Ideal.span {ϖ}) ((Ideal.Quotient.mk mI).comp iota) hI
  haveI : Nontrivial (R ⧸ mI) :=
    ⟨⟨1, 0, fun e => hm1 (Ideal.Quotient.eq_zero_iff_mem.mp ((map_one (Ideal.Quotient.mk mI)).trans e))⟩⟩
  letI : Algebra (V ⧸ (Ideal.span {ϖ} : Ideal V)) (R ⧸ mI) := phi.toAlgebra
  haveI : IsScalarTower V (V ⧸ (Ideal.span {ϖ} : Ideal V)) (R ⧸ mI) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective
    (Algebra.linearMap (V ⧸ (Ideal.span {ϖ} : Ideal V)) (R ⧸ mI)) (LinearMap.ker_eq_bot.mpr phi.injective)
  have hlam1 : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let mu : R →ₗ[V] V ⧸ (Ideal.span {ϖ} : Ideal V) :=
    (lam.restrictScalars V) ∘ₗ (Ideal.Quotient.mkₐ V mI).toLinearMap
  let incl : R →ₗ[V] F :=
    { toFun := fun x => (x : F)
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        show ((c • x : R) : F) = c • (x : F)
        rw [Algebra.smul_def, Algebra.smul_def]
        rfl }
  have hincl : Function.Injective incl := Subtype.val_injective
  let b' : Fin n → R := fun i => ⟨b i, (hb i).le⟩
  have hR : a ⊗ₜ[V] (1 : R) = ∑ i, c i ⊗ₜ[V] b' i := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := A) incl hincl
    simp only [map_sum, LinearMap.lTensor_tmul]
    exact h
  have hmu1 : mu 1 = 1 := by
    show lam (Ideal.Quotient.mk mI 1) = 1
    rw [map_one, hlam1]
  have hmub : ∀ i, mu (b' i) = 0 := by
    intro i
    show lam (Ideal.Quotient.mk mI (b' i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hb i), map_zero]
  have hk : a ⊗ₜ[V] (1 : V ⧸ (Ideal.span {ϖ} : Ideal V)) = 0 := by
    have e := congrArg (LinearMap.lTensor A mu) hR
    simp only [map_sum, LinearMap.lTensor_tmul, hmu1, hmub, TensorProduct.tmul_zero,
      Finset.sum_const_zero] at e
    exact e
  have hq : (Submodule.Quotient.mk a : A ⧸ (Ideal.span {ϖ} : Ideal V) • (⊤ : Submodule V A)) = 0 := by
    rw [← (TensorProduct.tensorQuotEquivQuotSMul A (Ideal.span {ϖ})).apply_symm_apply
      (Submodule.Quotient.mk a), TensorProduct.tensorQuotEquivQuotSMul_symm_mk, hk, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hq
  obtain ⟨y, -, hy⟩ := hq
  exact ⟨y, by rw [← hy, Algebra.smul_def]⟩

variable {V : Type} [CommRing V] {X Z : Scheme.{0}}

def cst (q : Z ⟶ Sp V) (z : Z) (a : V) : Z.presheaf.stalk z := gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)

private lemma germ_app_presheaf_map_eq_germ_app {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (a : Γ(B, U)) :
    (A.presheaf.germ (f ⁻¹ᵁ V) y hy).hom ((f.app V).hom ((B.presheaf.map (homOfLE hVU).op).hom a)) =
      (A.presheaf.germ (f ⁻¹ᵁ U) y (hVU hy)).hom ((f.app U).hom a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.Hom.naturality f (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat
  rw [nat]
  first
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _ _
    | (erw [TopCat.Presheaf.germ_res_apply])
    | (simp; done)

private lemma germ_app_app_eq_germ_app_comp {A B C : Scheme.{0}} (r : A ⟶ B) (h : B ⟶ C) (y : A) (W : C.Opens)
    (hy : h (r y) ∈ W) (a : Γ(C, W)) :
    (A.presheaf.germ (r ⁻¹ᵁ h ⁻¹ᵁ W) y hy).hom ((r.app (h ⁻¹ᵁ W)).hom ((h.app W).hom a)) =
      (A.presheaf.germ ((r ≫ h) ⁻¹ᵁ W) y hy).hom (((r ≫ h).app W).hom a) := by
  first
    | rfl
    | (simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; rfl)
    | (simp [Scheme.Hom.comp_app]; done)

theorem gs_appLE {Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f := by
  unfold gs
  rw [dif_pos hz, dif_pos (show (r ≫ q) z ∈ U from e hz)]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (germ_app_presheaf_map_eq_germ_app r z e hz _).trans (germ_app_app_eq_germ_app_comp r q z U (e hz) f)

theorem gs_constFn (p : X ⟶ Sp V) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : V) :
    gs r z W (constFn p W a) = cst (r ≫ p) z a := by
  first
    | (unfold constFn cst; exact gs_appLE p ⊤ W le_top r z hz _)
    | (unfold constFn cst; rw [← gs_appLE p ⊤ W le_top r z hz]; rfl)
    | (simp only [constFn, cst]; exact gs_appLE p ⊤ W le_top r z hz _)

theorem gs_stalkMap (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  unfold gs
  rw [dif_pos h, dif_pos (show (𝟙 X : X ⟶ X) (r z) ∈ U from h)]
  rw [← Scheme.Hom.germ_stalkMap_apply]
  first
  | rfl
  | (congr 1; simp)

theorem dvd_descend (r : Z ⟶ X) [Flat r] (z : Z) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  letI : Algebra (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) := (r.stalkMap z).hom.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  haveI : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton] at h ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Z.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
  exact h

theorem cst_regular [IsDomain V] (p : X ⟶ Sp V) [Flat p] (x : X) {a : V} (ha : a ≠ 0) : IsLeftRegular (cst p x a) := by
  have hU : IsAffineOpen (⊤ : (Sp V).Opens) := isAffineOpen_top _
  let y : (⊤ : (Sp V).Opens) := ⟨p x, trivial⟩
  haveI := hU.isLocalization_stalk y
  letI : Algebra Γ(Sp V, ⊤) ((Sp V).presheaf.stalk (p x)) :=
    TopCat.Presheaf.algebra_section_stalk (Sp V).presheaf y
  have hloc : Module.Flat Γ(Sp V, ⊤) ((Sp V).presheaf.stalk (p x)) :=
    IsLocalization.flat _ (hU.primeIdealOf y).asIdeal.primeCompl
  have hg : ((Sp V).presheaf.germ ⊤ (p x) trivial).hom.Flat :=
    RingHom.flat_algebraMap_iff.mpr hloc
  have hi : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)
  let φ : V →+* X.presheaf.stalk x :=
    (p.stalkMap x).hom.comp (((Sp V).presheaf.germ ⊤ (p x) trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)
  have hφ : φ.Flat := (hi.comp hg).comp (Flat.stalkMap p x)
  have hφe : ∀ b, φ b = cst p x b := by
    intro b
    change (p.stalkMap x).hom (((Sp V).presheaf.germ ⊤ (p x) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      gs p x ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    unfold gs
    rw [dif_pos (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
    exact Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial _
  letI : Algebra V (X.presheaf.stalk x) := φ.toAlgebra
  haveI : Module.Flat V (X.presheaf.stalk x) := hφ
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero ha)
  intro s s' hss
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hφe]
  exact hss

theorem exists_div [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) (W : X.Opens) (f : Γ(X, W))
    (h : ∀ x ∈ W, cst p x a ∣ gs (𝟙 X) x W f) : ∃ g : Γ(X, W), f = constFn p W a * g := by
  classical
  have hgs : ∀ {U : X.Opens} (x : X) (hx : x ∈ U) (s : Γ(X, U)),
      gs (𝟙 X) x U s = (X.presheaf.germ U x hx).hom s := by
    intro U x hx s
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) x ∈ U from hx)]
    rfl
  have hcst : ∀ {U : X.Opens} (x : X) (hx : x ∈ U),
      (X.presheaf.germ U x hx).hom (constFn p U a) = cst p x a := by
    intro U x hx
    rw [← hgs x hx, gs_constFn p U (𝟙 X) x hx a, Category.id_comp]
  have hmap : ∀ {A B : X.Opens} (i j : A ⟶ B) (s : Γ(X, B)),
      (X.presheaf.map i.op).hom s = (X.presheaf.map j.op).hom s := by
    intro A B i j s
    rw [Subsingleton.elim i j]
  have hmapc : ∀ {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (s : Γ(X, C)),
      (X.presheaf.map i.op).hom ((X.presheaf.map j.op).hom s) = (X.presheaf.map (i ≫ j).op).hom s := by
    intro A B C i j s
    rw [op_comp, Functor.map_comp]
    rfl
  have hres : ∀ {U V : X.Opens} (i : V ⟶ U),
      (X.presheaf.map i.op).hom (constFn p U a) = constFn p V a := by
    intro U V i
    apply TopCat.Presheaf.section_ext X.sheaf V
    intro y hy
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf i y hy (constFn p U a)
    have e2 := hcst y hy
    have e3 := hcst (U := U) y (i.le hy)
    exact e1.trans (e3.trans e2.symm)
  have hcancel : ∀ (U : X.Opens) (s t : Γ(X, U)), constFn p U a * s = constFn p U a * t → s = t := by
    intro U s t hst
    apply TopCat.Presheaf.section_ext X.sheaf U s t
    intro x hx
    apply cst_regular p x ha
    have e := congrArg (X.presheaf.germ U x hx).hom hst
    rw [map_mul, map_mul, hcst x hx] at e
    exact e
  have hloc : ∀ y : W, ∃ (U : X.Opens) (_ : (y : X) ∈ U) (iU : U ⟶ W) (g : Γ(X, U)),
      (X.presheaf.map iU.op).hom f = constFn p U a * g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := h x hx
    obtain ⟨U₁, hx₁, g₁, hg₁⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    have he : (X.presheaf.germ W x hx).hom f = (X.presheaf.germ U₁ x hx₁).hom (constFn p U₁ a * g₁) := by
      rw [map_mul, hcst x hx₁, ← hgs x hx, hc]
      exact congrArg _ hg₁.symm
    obtain ⟨U, hxU, iW, i1, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx₁ f _ he
    refine ⟨U, hxU, iW, (X.presheaf.map i1.op).hom g₁, ?_⟩
    rw [heq, map_mul, hres]
  choose U hxU iU g hg using hloc
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf U g := by
    intro x y
    apply hcancel
    rw [← hres (TopologicalSpace.Opens.infLELeft (U x) (U y)), ← map_mul, ← hg x, hmapc]
    conv_rhs => rw [hres, ← hres (TopologicalSpace.Opens.infLERight (U x) (U y)), ← map_mul, ← hg y, hmapc]
    exact hmap _ _ f
  obtain ⟨g', hg', -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U W iU
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU _⟩) g hcomp
  obtain ⟨g'', hg''⟩ : ∃ g'' : Γ(X, W), ∀ i, (X.presheaf.map (iU i).op).hom g'' = g i := ⟨g', hg'⟩
  refine ⟨g'', ?_⟩
  apply TopCat.Presheaf.section_ext X.sheaf W
  intro x hx
  have e1 : (X.presheaf.germ (U ⟨x, hx⟩) x (hxU _)).hom ((X.presheaf.map (iU ⟨x, hx⟩).op).hom f) =
      (X.presheaf.germ W x hx).hom f :=
    TopCat.Presheaf.germ_res_apply X.presheaf (iU ⟨x, hx⟩) x (hxU _) f
  have e2 : (X.presheaf.germ (U ⟨x, hx⟩) x (hxU _)).hom
      ((X.presheaf.map (iU ⟨x, hx⟩).op).hom (constFn p W a * g'')) =
      (X.presheaf.germ W x hx).hom (constFn p W a * g'') :=
    TopCat.Presheaf.germ_res_apply X.presheaf (iU ⟨x, hx⟩) x (hxU _) (constFn p W a * g'')
  change (X.presheaf.germ W x hx).hom f = (X.presheaf.germ W x hx).hom (constFn p W a * g'')
  rw [← e1, ← e2, hg, map_mul (X.presheaf.map (iU ⟨x, hx⟩).op).hom, hres, hg'']

private theorem presheaf_map_constFn' (p : X ⟶ Sp V) {A B : X.Opens} (i : B ⟶ A) (a : V) :
    (X.presheaf.map i.op).hom (constFn p A a) = constFn p B a := by
  apply TopCat.Presheaf.section_ext X.sheaf B
  intro y hy
  have hgs : ∀ {U : X.Opens} (hx : y ∈ U) (s : Γ(X, U)),
      gs (𝟙 X) y U s = (X.presheaf.germ U y hx).hom s := by
    intro U hx s
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) y ∈ U from hx)]
    rfl
  have hcst : ∀ {U : X.Opens} (hx : y ∈ U), (X.presheaf.germ U y hx).hom (constFn p U a) = cst p y a := by
    intro U hx
    rw [← hgs hx, gs_constFn p U (𝟙 X) y hx a, Category.id_comp]
  have e1 : (X.presheaf.germ B y hy).hom ((X.presheaf.map i.op).hom (constFn p A a)) =
      (X.presheaf.germ A y (i.le hy)).hom (constFn p A a) :=
    TopCat.Presheaf.germ_res_apply X.presheaf i y hy (constFn p A a)
  change (X.presheaf.germ B y hy).hom ((X.presheaf.map i.op).hom (constFn p A a)) =
    (X.presheaf.germ B y hy).hom (constFn p B a)
  rw [e1, hcst, hcst]

private theorem constFn_mul_left_cancel_of_flat [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) (U : X.Opens)
    (s t : Γ(X, U)) (hst : constFn p U a * s = constFn p U a * t) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf U s t
  intro x hx
  apply cst_regular p x ha
  have hgs : gs (𝟙 X) x U (constFn p U a) = (X.presheaf.germ U x hx).hom (constFn p U a) := by
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) x ∈ U from hx)]
    rfl
  have hcst : (X.presheaf.germ U x hx).hom (constFn p U a) = cst p x a := by
    rw [← hgs, gs_constFn p U (𝟙 X) x hx a, Category.id_comp]
  have e := congrArg (X.presheaf.germ U x hx).hom hst
  rw [map_mul, map_mul, hcst] at e
  exact e

theorem exists_div_sec [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) {M : LB X} (s : LB.Sec M)
    (h : ∀ j, ∀ x ∈ M.U j, cst p x a ∣ gs (𝟙 X) x (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ a * s'.f j := by
  choose g hg using fun j => exists_div p ha (M.U j) (s.f j) (h j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply constFn_mul_left_cancel_of_flat p ha
  rw [← presheaf_map_constFn' p (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) a, ← map_mul, ← hg i, s.compat i j]
  conv_rhs => rw [presheaf_map_constFn', mul_left_comm,
    ← presheaf_map_constFn' p (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)) a, ← map_mul, ← hg j]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
