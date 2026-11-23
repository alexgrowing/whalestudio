import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.SmallExtLift

variable {X Y Z : Scheme.{0}}

def gr (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gr_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gr f y V h ((X.presheaf.map (homOfLE hle).op).hom a) = gr f y U (hle h) a := by
  have e := congrArg (fun q => q.hom a) (f.naturality (homOfLE hle).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Y.presheaf.germ (f ⁻¹ᵁ V) y h).hom e).trans
    (TopCat.Presheaf.germ_res_apply Y.presheaf _ y h _)

theorem gr_app (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gr f z (g ⁻¹ᵁ U) h ((g.app U).hom a) = gr (f ≫ g) z U h a := rfl

theorem gr_appLE (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (h : f z ∈ V) (a : Γ(X, U)) :
    gr f z V h ((g.appLE U V e).hom a) = gr (f ≫ g) z U (e h) a :=
  gr_res f z e h _

theorem gr_congr {f g : Y ⟶ X} (e : f = g) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gr f y U h a = gr g y U (e ▸ h) a := by subst e; rfl

theorem gr_ext {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ x (hx : (𝟙 X : X ⟶ X) x ∈ V), gr (𝟙 X) x V hx a = gr (𝟙 X) x V hx b) : a = b :=
  TopCat.Presheaf.section_ext X.sheaf V _ _ h

theorem isUnit_of_gr {V : X.Opens} {a : Γ(X, V)}
    (h : ∀ x (hx : (𝟙 X : X ⟶ X) x ∈ V), IsUnit (gr (𝟙 X) x V hx a)) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ _ _ h

variable {R : Type} [CommRing R]

def cst (p : X ⟶ Spec (CommRingCat.of R)) (V : X.Opens) : R →+* Γ(X, V) :=
  (p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def cstS (p : X ⟶ Spec (CommRingCat.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  (gr p x ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gr_cst (f : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of R)) (z : Z) (V : X.Opens) (h : f z ∈ V)
    (r : R) : gr f z V h (cst p V r) = cstS (f ≫ p) z r :=
  gr_appLE f p z ⊤ V le_top h _

theorem cstS_comp {R' : Type} [CommRing R'] (φ : R →+* R') (p : X ⟶ Spec (CommRingCat.of R'))
    (x : X) (r : R) :
    cstS (p ≫ Spec.map (CommRingCat.ofHom φ)) x r = cstS p x (φ r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  exact congrArg (gr p x ⊤ trivial) e.symm

section Quot
variable {R' : Type} [CommRing R'] {φ : R →+* R'} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of R')}

theorem app_surj (hφ : Function.Surjective φ)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom φ))) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (π.app V).hom := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  have : IsClosedImmersion π := MorphismProperty.of_isPullback H.flip this
  exact π.app_surjective V hV

theorem app_cst (H : π ≫ p = f' ≫ Spec.map (CommRingCat.ofHom φ)) (V : X.Opens) (r : R) :
    (π.app V).hom (cst p V r) = cst f' (π ⁻¹ᵁ V) (φ r) := by
  refine gr_ext fun y hy => ?_
  rw [gr_app, gr_cst, gr_cst, Category.id_comp, Category.id_comp, H, cstS_comp]

theorem mem_of_app_eq_zero (hφ : Function.Surjective φ)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom φ))) {V : X.Opens} (hV : IsAffineOpen V)
    (a : Γ(X, V)) (ha : (π.app V).hom a = 0) : a ∈ (RingHom.ker φ).map (cst p V) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  set J := (RingHom.ker φ).map (cst p V)
  let l : R' →+* Γ(X, V) ⧸ J := φ.liftOfSurjective hφ ⟨(Ideal.Quotient.mk J).comp (cst p V),
    fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hl : ∀ r, l (φ r) = Ideal.Quotient.mk J (cst p V r) := fun r =>
    φ.liftOfSurjective_comp_apply hφ _ r
  have w : p.appLE ⊤ V le_top ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top ≫
        (Scheme.ΓSpecIso (CommRingCat.of R')).hom ≫ CommRingCat.ofHom l := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom φ)).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    exact (hl r).symm
  have e := congrArg (fun q => q.hom a) (po.inl_desc _ _ w)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Scheme.Hom.appLE_eq_app, ha, map_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm

end Quot

theorem mem_of_flat [IsLocalRing R] {ε : R} (hε : ε ≠ 0) {B : Type} [CommRing B] (c : R →+* B)
    (hf : c.Flat) (a : B) (ha : c ε * a = 0) : a ∈ (IsLocalRing.maximalIdeal R).map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => a)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact ha)
  have : a = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c ?_)
  have h := hc j
  rw [Fintype.sum_unique] at h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hε (hu.mul_left_eq_zero.1 h)

theorem cst_flat (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] {V : X.Opens} (hV : IsAffineOpen V) : (cst p V).Flat :=
  RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
    (p.flat_appLE (isAffineOpen_top _) hV le_top)

theorem mul_eq_zero_of_mem {B : Type*} [CommRing B] (c : R →+* B) {I : Ideal R} {ε : R}
    (h : ∀ a ∈ I, a * ε = 0) {b : B} (hb : b ∈ I.map c) : c ε * b = 0 := by
  have : I.map c ≤ RingHom.ker (RingHom.id B) ⊔ (Ideal.span {c ε}).annihilator := by
    refine le_sup_of_le_right (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
    rw [Ideal.mem_comap, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul,
      ← map_mul, h a ha, map_zero]
  have h2 := this hb
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (fun _ _ e => e), bot_sup_eq, Ideal.span,
    Submodule.mem_annihilator_span_singleton, smul_eq_mul] at h2
  rw [mul_comm, h2]

theorem gr_cocycle {M : LB X} (hM : M.IsLB) (f : Z ⟶ X) (z : Z) {i j k : M.ι} (hi : f z ∈ M.U i)
    (hj : f z ∈ M.U j) (hk : f z ∈ M.U k) :
    gr f z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val * gr f z (M.U j ⊓ M.U k) ⟨hj, hk⟩ (M.g j k).val =
      gr f z (M.U i ⊓ M.U k) ⟨hi, hk⟩ (M.g i k).val := by
  have hm : f z ∈ M.U i ⊓ M.U j ⊓ M.U k := ⟨⟨hi, hj⟩, hk⟩
  have := congrArg (fun u => gr f z _ hm u.val) (hM.cocycle i j k)
  simp only [Units.val_mul, map_mul] at this
  exact (congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)).symm.trans
    (this.trans (gr_res f z _ hm _))

theorem pull_le (M : LB X) (F : Y ⟶ X) (i : M.ι) {V : X.Opens} (h : V ≤ M.U i) :
    F ⁻¹ᵁ V ≤ (M.pull F).U (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

theorem gr_gen {M : LB X} {F : Y ⟶ X} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {i j : M.ι} (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j) :
    gr r z _ (pull_le M F i le_rfl hi) (t.s fun _ => i).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val *
        gr r z _ (pull_le M F j le_rfl hj) (t.s fun _ => j).val := by
  have hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j) :=
    ⟨pull_le M F i le_rfl hi, pull_le M F j le_rfl hj⟩
  have := congrArg (fun u => gr r z _ hm u.val) (ht (fun _ => i) (fun _ => j))
  simp only [Units.val_mul, map_mul] at this
  refine (gr_res r z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) ?_ (gr_res r z _ hm _)))
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _

theorem gen_of_refine {M : LB X} (hM : M.IsLB) {I : Type} (V : I → X.Opens) (hV : ⨆ a, V a = ⊤)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (w : ∀ a, Γ(X, V a)) (hw : ∀ a, IsUnit (w a))
    (H : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      gr (𝟙 X) x _ ha (w a) = gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩
        (M.g (j a) (j b)).val * gr (𝟙 X) x _ hb (w b)) :
    ∃ t : LB.Gen M, t.IsGen := by
  have cov : ∀ x : X, ∃ a, x ∈ V a := fun x =>
    Opens.mem_iSup.1 (show x ∈ ⨆ a, V a by rw [hV]; trivial)
  have glue : ∀ i : M.ι, ∃ s : Γ(X, M.U i), ∀ a x (hi : (𝟙 X : X ⟶ X) x ∈ M.U i)
      (ha : (𝟙 X : X ⟶ X) x ∈ V a), gr (𝟙 X) x _ hi s =
        gr (𝟙 X) x (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr (𝟙 X) x _ ha (w a) := by
    intro i
    let u : ∀ a, Γ(X, M.U i ⊓ V a) := fun a =>
      (X.presheaf.map (homOfLE (inf_le_inf_left _ (hj a))).op).hom (M.g i (j a)).val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom (w a)
    have hu : ∀ a x (h : (𝟙 X : X ⟶ X) x ∈ M.U i ⊓ V a), gr (𝟙 X) x _ h (u a) =
        gr (𝟙 X) x (M.U i ⊓ M.U (j a)) ⟨h.1, hj a h.2⟩ (M.g i (j a)).val *
          gr (𝟙 X) x _ h.2 (w a) := fun a x h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ x _ h _) (gr_res _ x _ h _))
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun a => M.U i ⊓ V a) (M.U i)
      (fun a => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨a, ha⟩ := cov x
        exact Opens.mem_iSup.2 ⟨a, hx, ha⟩) u
      (fun a b => gr_ext (V := (M.U i ⊓ V a) ⊓ (M.U i ⊓ V b)) fun x hx => by
        refine (gr_res _ x inf_le_left hx _).trans
          (Eq.trans ?_ (gr_res _ x inf_le_right hx _).symm)
        refine (hu a x hx.1).trans (Eq.trans ?_ (hu b x hx.2).symm)
        rw [H a b x hx.1.2 hx.2.2, ← _root_.mul_assoc,
          gr_cocycle hM _ x hx.1.1 (hj a hx.1.2) (hj b hx.2.2)])
    refine ⟨s, fun a x hi ha => ?_⟩
    have hm : (𝟙 X : X ⟶ X) x ∈ M.U i ⊓ V a := ⟨hi, ha⟩
    exact (gr_res _ x inf_le_left hm s).symm.trans ((congrArg (gr _ x _ hm) (hs a)).trans (hu a x hm))
  choose s hs using glue
  have hu : ∀ i, IsUnit (s i) := fun i => isUnit_of_gr fun x hx => by
    obtain ⟨a, ha⟩ := cov x
    rw [hs i a x hx ha]
    exact ((Units.isUnit _).map _).mul ((hw a).map _)
  refine ⟨⟨fun i => (hu i).unit⟩, fun i k => Units.ext (gr_ext fun x hx => ?_)⟩
  obtain ⟨a, ha⟩ := cov x
  refine (gr_res _ x inf_le_left hx (s i)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gr_res _ x inf_le_right hx (s k)))).symm)
  rw [hs i a x hx.1 ha, hs k a x hx.2 ha, ← _root_.mul_assoc, ← gr_cocycle hM _ x hx.1 hx.2 (hj a ha)]

theorem isUnit_one_add {B : Type*} [CommRing B] {e : B} (he : e * e = 0) (b : B) :
    IsUnit (1 + e * b) :=
  IsUnit.of_mul_eq_one (1 - e * b) (by linear_combination (-(b * b)) * he)

section Eps
variable {ε : R} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}

theorem exists_eq_mul
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : (π.app V).hom a = 0) :
    ∃ b, a = cst p V ε * b := by
  have := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H hV a ha
  rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
  exact this

theorem isUnit_of_app (hε : ε * ε = 0)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : IsUnit ((π.app V).hom a)) :
    IsUnit a := by
  obtain ⟨v', hv'⟩ := ha.exists_right_inv
  obtain ⟨v, rfl⟩ := app_surj Ideal.Quotient.mk_surjective H hV v'
  obtain ⟨b, hb⟩ := exists_eq_mul H hV (a * v - 1) (by rw [map_sub, map_mul, hv', map_one, sub_self])
  have := isUnit_one_add (e := cst p V ε) (by rw [← map_mul, hε, map_zero]) b
  rw [← hb, add_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left this

end Eps

def Rel (p : X ⟶ Spec (CommRingCat.of R)) (ε : R) (M : LB X) {I : Type} (V : I → X.Opens)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u : ∀ a, Γ(X, V a))
    (α : ∀ a b, Γ(X, V a ⊓ V b)) : Prop :=
  ∀ a b (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (ha : f z ∈ V a) (hb : f z ∈ V b),
    gr f z _ ha (u a) = gr f z (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩ (M.g (j a) (j b)).val *
      gr f z _ hb (u b) * (1 + cstS (f ≫ p) z ε * gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b))

theorem exists_lift {ε : R} (hε : ε * ε = 0) {p : X ⟶ Spec (CommRingCat.of R)} [X.IsSeparated]
    {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {M : LB X} (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ (I : Type) (V : I → X.Opens) (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
      (u : ∀ a, Γ(X, V a)) (α : ∀ a b, Γ(X, V a ⊓ V b)),
      ⨆ a, V a = ⊤ ∧ (∀ a, IsAffineOpen (V a)) ∧ (∀ a, IsUnit (u a)) ∧ Rel p ε M V j hj u α := by
  let I := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : I → X.Opens := fun a => a.1.2
  let j : I → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hV : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  choose u hu using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    ((Y.presheaf.map (homOfLE (pull_le M π (j a) (hj a))).op).hom (t.s fun _ => j a).val)
  have uu : ∀ a, IsUnit (u a) := fun a => isUnit_of_app hε H (hV a) _ (by
    rw [hu]; exact (Units.isUnit _).map _)
  have key : ∀ a b, ∃ α : Γ(X, V a ⊓ V b), (X.presheaf.map (homOfLE inf_le_left).op).hom (u a) =
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom (M.g (j a) (j b)).val *
      (X.presheaf.map (homOfLE inf_le_right).op).hom (u b) * (1 + cst p _ ε * α) := by
    intro a b
    obtain ⟨c, hc⟩ := exists_eq_mul H ((hV a).inf (hV b))
      ((X.presheaf.map (homOfLE inf_le_left).op).hom (u a) -
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom (M.g (j a) (j b)).val *
      (X.presheaf.map (homOfLE inf_le_right).op).hom (u b)) (gr_ext fun y hy => by
        have e : ∀ c (h : (𝟙 Y ≫ π) y ∈ V c), gr (𝟙 Y ≫ π) y (V c) h (u c) =
            gr (𝟙 Y) y _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π y (V c) h (u c)).symm.trans ((congrArg _ (hu c)).trans (gr_res (𝟙 Y) y _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) y (hj a hy.1) (hj b hy.2))
    obtain ⟨v, hv⟩ := (((Units.isUnit (M.g (j a) (j b))).map
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom).mul ((uu b).map
      (X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ _)).op).hom)).exists_right_inv
    exact ⟨v * c, by linear_combination hc - (cst p _ ε * c) * hv⟩
  choose α hα using key
  refine ⟨I, V, j, hj, u, α, eq_top_iff.2 fun x _ => ?_, hV, uu, fun a b Z f z ha hb => ?_⟩
  · obtain ⟨i, hi⟩ := TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  · have := congrArg (gr f z (V a ⊓ V b) ⟨ha, hb⟩) (hα a b)
    rwa [map_mul, map_mul, map_add, map_one, map_mul, gr_res, gr_res, gr_res, gr_cst] at this

section RelLemmas
variable {p : X ⟶ Spec (CommRingCat.of R)} {ε : R} {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}

theorem Rel.cocycle (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB)
    (hu : ∀ a, IsUnit (u a)) (a b d : I) (f : Z ⟶ X) (z : Z) (ha : f z ∈ V a) (hb : f z ∈ V b)
    (hd : f z ∈ V d) :
    cstS (f ≫ p) z ε * (gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr f z (V b ⊓ V d) ⟨hb, hd⟩ (α b d) -
      gr f z (V a ⊓ V d) ⟨ha, hd⟩ (α a d)) = 0 := by
  have h1 := H a b _ f z ha hb
  have h2 := H b d _ f z hb hd
  have h3 := H a d _ f z ha hd
  have hc := gr_cocycle hM f z (hj a ha) (hj b hb) (hj d hd)
  have he : cstS (f ≫ p) z ε * cstS (f ≫ p) z ε = 0 := by rw [← map_mul, hε, map_zero]
  have un := ((Units.isUnit (M.g (j a) (j d))).map
    (gr f z (M.U (j a) ⊓ M.U (j d)) ⟨hj a ha, hj d hd⟩)).mul ((hu d).map (gr f z _ hd))
  refine un.mul_right_eq_zero.1 ?_
  rw [h1, h2] at h3
  generalize gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b) = x₁ at *
  generalize gr f z (V b ⊓ V d) ⟨hb, hd⟩ (α b d) = x₂ at *
  generalize gr f z (V a ⊓ V d) ⟨ha, hd⟩ (α a d) = x₃ at *
  generalize cstS (f ≫ p) z ε = e at *
  generalize gr f z _ hd (u d) = v at *
  rw [← hc] at h3 ⊢
  generalize gr f z (M.U (j a) ⊓ M.U (j b)) _ _ = g₁ at *
  generalize gr f z (M.U (j b) ⊓ M.U (j d)) _ _ = g₂ at *
  linear_combination h3 - (g₁ * g₂ * v * x₁ * x₂) * he

theorem Rel.gen (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB) (hV : ⨆ a, V a = ⊤)
    (hu : ∀ a, IsUnit (u a)) (β : ∀ a, Γ(X, V a))
    (hβ : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      cstS (𝟙 X ≫ p) x ε * (gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 X) x _ ha (β a) - gr (𝟙 X) x _ hb (β b))) = 0) :
    ∃ t : LB.Gen M, t.IsGen := by
  refine gen_of_refine hM V hV j hj (fun a => u a * (1 + cst p _ ε * (-β a)))
    (fun a => (hu a).mul (isUnit_one_add (by rw [← map_mul, hε, map_zero]) _))
    fun a b x ha hb => ?_
  have he : cstS (𝟙 X ≫ p) x ε * cstS (𝟙 X ≫ p) x ε = 0 := by rw [← map_mul, hε, map_zero]
  have h := hβ a b x ha hb
  simp only [map_mul, map_add, map_one, map_neg, gr_cst]
  rw [H a b _ _ x ha hb]
  generalize gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) = x₁ at *
  generalize gr (𝟙 X) x _ ha (β a) = x₂ at *
  generalize gr (𝟙 X) x _ hb (β b) = x₃ at *
  generalize cstS (𝟙 X ≫ p) x ε = e at *
  generalize gr (𝟙 X) x _ hb (u b) = v at *
  generalize gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) _ _ = g₁ at *
  linear_combination (g₁ * v) * h - (g₁ * v * x₁ * x₂) * he

theorem Rel.slice (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) :
    ∃ β : ∀ a, Γ(A, s ⁻¹ᵁ V a), ∀ a b x (ha : s ((𝟙 A : A ⟶ A) x) ∈ V a)
      (hb : s ((𝟙 A : A ⟶ A) x) ∈ V b),
      cstS ((𝟙 A ≫ s) ≫ p) x ε * (gr (𝟙 A ≫ s) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 A) x (s ⁻¹ᵁ V a) ha (β a) - gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (β b))) = 0 := by
  let r : ∀ a, Γ(A, s ⁻¹ᵁ V a) := fun a => (s.app (V a)).hom (u a) *
    (A.presheaf.map (homOfLE (pull_le M s (j a) (hj a))).op).hom (t.s fun _ => j a)⁻¹.val
  have ru : ∀ a, IsUnit (r a) := fun a => ((hu a).map _).mul ((Units.isUnit _).map _)
  have hr : ∀ a b (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (ha : s (f z) ∈ V a) (hb : s (f z) ∈ V b),
      gr f z (s ⁻¹ᵁ V a) ha (r a) = gr f z (s ⁻¹ᵁ V b) hb (r b) *
        (1 + cstS ((f ≫ s) ≫ p) z ε * gr (f ≫ s) z (V a ⊓ V b) ⟨ha, hb⟩ (α a b)) := by
    intro a b Z f z ha hb
    have h1 := H a b _ (f ≫ s) z ha hb
    have h2 := gr_gen ht f z (hj a ha) (hj b hb)
    have i1 := congrArg (gr f z _ (pull_le M s (j a) le_rfl (hj a ha))) (t.s fun _ => j a).mul_inv
    have i2 := congrArg (gr f z _ (pull_le M s (j b) le_rfl (hj b hb))) (t.s fun _ => j b).mul_inv
    rw [map_mul, map_one] at i1 i2
    simp only [r, map_mul]
    rw [gr_res, gr_res, gr_app, gr_app, h1]
    rw [h2] at i1
    generalize gr f z _ (pull_le M s (j a) le_rfl (hj a ha)) (t.s fun _ => j a)⁻¹.val = ta at *
    generalize gr f z _ (pull_le M s (j b) le_rfl (hj b hb)) (t.s fun _ => j b)⁻¹.val = tb at *
    generalize gr f z _ (pull_le M s (j b) le_rfl (hj b hb)) (t.s fun _ => j b).val = sb at *
    generalize gr (f ≫ s) z (M.U (j a) ⊓ M.U (j b)) _ _ = g at *
    generalize (1 + cstS ((f ≫ s) ≫ p) z ε * gr (f ≫ s) z (V a ⊓ V b) ⟨ha, hb⟩ (α a b)) = w at *
    generalize gr (f ≫ s) z (V b) _ (u b) = v at *
    linear_combination (v * w * tb) * i1 - (g * v * w * ta) * i2
  have cov : ⨆ a, π ⁻¹ᵁ s ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hV]; rfl
  obtain ⟨c', hc'⟩ := TLinPf.glue (fun a => π ⁻¹ᵁ s ⁻¹ᵁ V a) cov (fun a => (π.app _).hom (r a))
    (fun a b => gr_ext fun y hy => by
      rw [gr_res, gr_res, gr_app, gr_app, hr a b _ (𝟙 _ ≫ π) y hy.1 hy.2]
      have : ((𝟙 A' ≫ π) ≫ s) ≫ p = f' ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {ε}))) := by rw [← P.w]; simp
      rw [this, cstS_comp, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε),
        map_zero, zero_mul, add_zero, _root_.mul_one])
  obtain ⟨c₁, rfl⟩ := hf c'
  obtain ⟨c₂, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {ε}))).inv).2 c₁
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c₂
  have key : ∀ a, ∃ β : Γ(A, s ⁻¹ᵁ V a), cst (s ≫ p) (s ⁻¹ᵁ V a) c =
      r a * (1 + cst (s ≫ p) (s ⁻¹ᵁ V a) ε * -β) := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_mul P ((hA a).preimage s) (r a - cst (s ≫ p) _ c) (by
      rw [map_sub, app_cst P.w, ← hc' a, sub_eq_zero]; rfl)
    obtain ⟨v, hv⟩ := (ru a).exists_right_inv
    refine ⟨v * b, ?_⟩
    generalize cst (s ≫ p) (s ⁻¹ᵁ V a) c = c₀ at *
    generalize cst (s ≫ p) (s ⁻¹ᵁ V a) ε = e at *
    generalize r a = ρ at *
    linear_combination (e * b) * hv - hb
  choose β hβ using key
  refine ⟨β, fun a b x ha hb => ?_⟩
  have h1 := hr a b _ (𝟙 A) x ha hb
  have h2 := congrArg (gr (𝟙 A) x (s ⁻¹ᵁ V a) ha) (hβ a)
  have h3 := congrArg (gr (𝟙 A) x (s ⁻¹ᵁ V b) hb) (hβ b)
  simp only [map_mul, map_add, map_one, map_neg, gr_cst, ← Category.assoc] at h2 h3
  have he : cstS ((𝟙 A ≫ s) ≫ p) x ε * cstS ((𝟙 A ≫ s) ≫ p) x ε = 0 := by
    rw [← map_mul, hε, map_zero]
  refine ((ru b).map (gr (𝟙 A) x (s ⁻¹ᵁ V b) hb)).mul_right_eq_zero.1 ?_
  rw [h2, h1] at h3
  generalize gr (𝟙 A ≫ s) x (V a ⊓ V b) _ (α a b) = x₁ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V a) ha (β a) = x₂ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (β b) = x₃ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (r b) = v at *
  generalize cstS ((𝟙 A ≫ s) ≫ p) x ε = e at *
  linear_combination h3 + (v * x₁ * x₂) * he

end RelLemmas

section Residue
variable [IsLocalRing R] {ε : R} {p : X ⟶ Spec (CommRingCat.of R)} {i : Y ⟶ X}
  {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}

theorem app_eq_zero_of_mul (hε : ε ≠ 0) [Flat p]
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : cst p V ε * a = 0) :
    (i.app V).hom a = 0 := by
  have h := mem_of_flat hε _ (cst_flat p hV) a ha
  refine (show _ ≤ RingHom.ker (i.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
  rw [Ideal.mem_comap, RingHom.mem_ker, app_cst w, (IsLocalRing.residue_eq_zero_iff r).2 hr,
    map_zero]

theorem mul_eq_zero_of_app (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    (P : IsPullback i f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : (i.app V).hom a = 0) :
    cst p V ε * a = 0 := by
  have h := mem_of_app_eq_zero IsLocalRing.residue_surjective P hV a ha
  rw [IsLocalRing.ker_residue] at h
  exact mul_eq_zero_of_mem _ hm h

variable {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}

theorem Rel.cocycle_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0) [Flat p]
    [X.IsSeparated] (hM : M.IsLB) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (a b d : I) (y : Y)
    (ha : (𝟙 Y ≫ i) y ∈ V a) (hb : (𝟙 Y ≫ i) y ∈ V b) (hd : (𝟙 Y ≫ i) y ∈ V d) :
    gr (𝟙 Y ≫ i) y (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr (𝟙 Y ≫ i) y (V b ⊓ V d) ⟨hb, hd⟩ (α b d) =
      gr (𝟙 Y ≫ i) y (V a ⊓ V d) ⟨ha, hd⟩ (α a d) := by
  have h := app_eq_zero_of_mul h0 w (((hA a).inf (hA b)).inf (hA d))
    ((X.presheaf.map (homOfLE inf_le_left).op).hom (α a b) +
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op).hom
        (α b d) -
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom
        (α a d)) (gr_ext fun x hx => by
      rw [map_mul, map_sub, map_add, gr_res, gr_res, gr_res, gr_cst, map_zero]
      exact H.cocycle hε hM hu a b d _ x hx.1.1 hx.1.2 hx.2)
  have h' := congrArg (gr (𝟙 Y) y (i ⁻¹ᵁ (V a ⊓ V b ⊓ V d)) ⟨⟨ha, hb⟩, hd⟩) h
  rw [gr_app, map_sub, map_add, gr_res, gr_res, gr_res, map_zero] at h'
  exact sub_eq_zero.1 h'

theorem Rel.slice_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0)
    [X.IsSeparated] (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' Ak : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    [Flat (s ≫ p)] {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) {iA : Ak ⟶ A}
    {fk : Ak ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (w : iA ≫ s ≫ p = fk ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (sk : Ak ⟶ Y) (e : sk ≫ i = iA ≫ s) :
    ∃ ψ : ∀ a, Γ(Ak, sk ⁻¹ᵁ i ⁻¹ᵁ V a), ∀ a b,
      (sk.app (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b)).hom
          ((i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b)) =
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V a from
          fun _ h => h.1)).op).hom (ψ a) -
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V b from
          fun _ h => h.2)).op).hom (ψ b) := by
  obtain ⟨β, hβ⟩ := H.slice hε hV hA s P hf hu t ht
  have le : ∀ a, sk ⁻¹ᵁ i ⁻¹ᵁ V a ≤ iA ⁻¹ᵁ s ⁻¹ᵁ V a := fun a => by
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  refine ⟨fun a => (iA.appLE _ _ (le a)).hom (β a), fun a b => gr_ext fun y hy => ?_⟩
  have h := app_eq_zero_of_mul h0 w (((hA a).inf (hA b)).preimage s)
    ((s.app _).hom (α a b) -
      ((A.presheaf.map (homOfLE (show s ⁻¹ᵁ (V a ⊓ V b) ≤ s ⁻¹ᵁ V a from fun _ h => h.1)).op).hom
        (β a) -
      (A.presheaf.map (homOfLE (show s ⁻¹ᵁ (V a ⊓ V b) ≤ s ⁻¹ᵁ V b from fun _ h => h.2)).op).hom
        (β b))) (gr_ext fun x hx => by
      rw [map_mul, map_sub, map_sub, gr_res, gr_res, gr_app, gr_cst, map_zero, ← Category.assoc]
      exact hβ a b x hx.1 hx.2)
  have h' := congrArg (gr (𝟙 Ak) y (iA ⁻¹ᵁ s ⁻¹ᵁ (V a ⊓ V b)) ⟨le a hy.1, le b hy.2⟩) h
  rw [gr_app, map_sub, map_sub, gr_res, gr_res, gr_app, map_zero] at h'
  rw [map_sub, gr_res, gr_res, gr_app, gr_appLE, gr_appLE, gr_appLE]
  refine Eq.trans (gr_congr ?_ _ _ _ _) (sub_eq_zero.1 h')
  simp [e]

theorem Rel.gen_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) [X.IsSeparated] (hM : M.IsLB)
    (hV : ⨆ a, V a = ⊤) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (P : IsPullback i f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (ψ : ∀ a, Γ(Y, i ⁻¹ᵁ V a))
    (hψ : ∀ a b, (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b) =
      (Y.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) -
        (Y.presheaf.map (homOfLE inf_le_right).op).hom (ψ b)) :
    ∃ t : LB.Gen M, t.IsGen := by
  choose β hβ using fun a => app_surj IsLocalRing.residue_surjective P (hA a) (ψ a)
  refine H.gen hε hM hV hu β fun a b x ha hb => ?_
  have h := mul_eq_zero_of_app hm P ((hA a).inf (hA b)) (α a b -
    ((X.presheaf.map (homOfLE inf_le_left).op).hom (β a) -
      (X.presheaf.map (homOfLE inf_le_right).op).hom (β b))) (gr_ext fun y hy => by
      have h' := congrArg (gr (𝟙 Y) y (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) hy) (hψ a b)
      rw [gr_appLE, map_sub, gr_res, gr_res, ← hβ, ← hβ, gr_app, gr_app] at h'
      rw [gr_app, map_sub, map_sub, gr_res, gr_res, map_zero]
      exact sub_eq_zero.2 h')
  have h' := congrArg (gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩) h
  rwa [map_mul, map_sub, map_sub, gr_res, gr_res, gr_cst, map_zero] at h'

end Residue

open scoped CategoryTheory.Obj in

theorem exists_gen_of_small_extension : GlobalFnsSt → (∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b)) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen := by
  intro hG hK R _ _ ε hm A _ hA M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have := hA.smooth
  have := hA.proper
  have sep : IsSeparated (A ⊗ A).hom := by
    change IsSeparated (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ A).hom := by
    change Flat (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have : (A ⊗ A).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ A).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have hk := TLinPf.isAb_pullback φ A hA
  have := hk.proper
  let i : (F.obj A ⊗ F.obj A).left ⟶ (A ⊗ A).left :=
    (Functor.Monoidal.μIso F A A).hom.left ≫ pullback.fst (A ⊗ A).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj A).hom (A ⊗ A).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ A).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A A).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A A).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A A).inv).symm
  have slice : ∀ (s : A ⟶ A ⊗ A) (r : A ⊗ A ⟶ A) [IsSeparated r.left], s ≫ r = 𝟙 A →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj A ⟶ F.obj A ⊗ F.obj A,
      sk ≫ (Functor.Monoidal.μIso F A A).hom = F.map s → _ := fun s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ A).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst A.hom q)
      (f' := pullback.snd A.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      (hG _ _ (TLinPf.isAb_pullback q A hA)).2 hu t ht (iA := pullback.fst A.hom φ)
      (fk := pullback.snd A.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : toUnit (F.obj A) ≫ η[F.obj A] = F.map (1 : A ⟶ A) := by
    rw [Functor.obj.η_def, Hom.one_def, F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := hK (IsLocalRing.ResidueField R) (F.obj A) (F.obj A) η[F.obj A] η[F.obj A]
    inferInstance inferInstance inferInstance inferInstance (hG _ _ hk) (hG _ _ hk) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice _ (fst A A) (by change IsSeparated (pullback.fst A.hom A.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice _ (snd A A) (by change IsSeparated (pullback.snd A.hom A.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ

end GlobalTheory.SmallExtLift
