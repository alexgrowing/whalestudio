import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

def Compat (φ : R →+* R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] : Prop :=
  ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
    algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))

theorem Compat.base (hF : Compat φ F) : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom :=
  ArcTransport.base_comm hF

theorem Compat.sq (hF : Compat φ F) : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R :=
  (Category.assoc _ _ _).symm.trans hF.base

theorem c_symm (y : D.X) : (D'.c (hD.xe.symm y)).left ≫ proj hD = spMap φ ≫ (D.c y).left := by
  have := hD.c_pr (hD.xe.symm y)
  rwa [AddEquiv.apply_symm_apply] at this

theorem pullGt_val {g : GtPtF D F} {g' : GtPtF D' F} (h : IsPullGtF φ hD F g g') (χ : D'.X) {Z : Scheme.{0}}
    (r : Z ⟶ Sp F) {z : Z} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (g.s (hD.xe χ)) r z J = (om hD.w z J J' (r ≫ (cP D' _ χ * g'.b).left))⁻¹ *
      om hD.w z J J' (r ≫ (cP D' (TF (R := R') F) χ).left) * om hD.w z J J' (r ≫ g'.b.left) *
      (om hD.w z J J' (r ≫ (1 : TF (R := R') F ⟶ D'.P.A).left))⁻¹ * val (g'.s χ) r z J' := by
  obtain ⟨hψ, hm⟩ := h.2 χ
  have pm := (maps_iff hD.w _ _ _ (g'.s χ) (g.s (hD.xe χ)) (𝟙 _) _
    (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm
  have e := pmaps_om hψ pm r z hJ hJ'
  exact (congrArg (fun q => val (g.s (hD.xe χ)) q z J) (Category.comp_id r).symm).trans <| e.trans (congrArg₂ (· * ·) (prod_gt g'.b χ (fun q => om hD.w z J J' (r ≫ q))) rfl)

theorem isPullGtF_of_val (hF : Compat φ F) {g : GtPtF D F} {g' : GtPtF D' F} (hb : g'.b.left ≫ proj hD = g.b.left)
    (h : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vS (g.s (hD.xe χ)) y J = (om hD.w y J J' (cP D' _ χ * g'.b).left)⁻¹ *
      om hD.w y J J' (cP D' (TF (R := R') F) χ).left * om hD.w y J J' g'.b.left *
      (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left)⁻¹ * vS (g'.s χ) y J') : IsPullGtF φ hD F g g' := by
  refine ⟨hb, fun χ => ?_⟩
  have hb' : ArcTransport.pushF (pull_grp hD) hF.base g'.b = g.b := Over.OverMorphism.ext hb
  have hψ : ∀ i, DegPre.gtφ D' F g'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F g.b (hD.xe χ) i := fun i => by
    have := ArcTransport.gtφ_push (pull_grp hD) hF.base (c_symm hD) g'.b (hD.xe χ) i
    rw [AddEquiv.symm_apply_apply, hb'] at this
    exact this.trans (Category.id_comp _).symm
  exact ⟨hψ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (g'.isGen χ) _ (g.isGen _) hψ
    fun y J J' hJ hJ' => (h χ y J J' hJ hJ').trans (congrArg₂ (· * ·)
      (prod_gt g'.b χ (fun r => om hD.w y J J' r)).symm rfl)⟩

theorem isPullGtF_iff (hF : Compat φ F) (g : GtPtF D F) (g' : GtPtF D' F) :
    IsPullGtF φ hD F g g' ↔ ArcTransport.GtRel hD.w hD.xe.symm (fun _ => 1) g g' := by
  rw [ArcTransport.gtRel_iff (pull_grp hD) hF.base (c_symm hD) ((isGen_iff _).1 hD.w_gen)]
  constructor
  · intro h
    refine ⟨Over.OverMorphism.ext h.1, fun χ y J J' hJ hJ' => ?_⟩
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    have e := pullGt_val hD h χ (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at e
    rw [AddEquiv.symm_apply_apply, map_one, _root_.one_mul]
    exact e.symm
  · rintro ⟨hb, h⟩
    refine isPullGtF_of_val hD hF (congrArg (fun q => q.left) hb) fun χ y J J' hJ hJ' => ?_
    have e := h (hD.xe χ) y J J' hJ hJ'
    rw [AddEquiv.symm_apply_apply, map_one, _root_.one_mul] at e
    exact e.symm

variable (hG : GlobalFnsSt) (hF : Compat φ F)

include hG hF in
theorem exists_pullGt (g : GtPtF D F) : ∃ g', IsPullGtF φ hD F g g' := by
  obtain ⟨g', h⟩ := ArcTransport.exists_gtRel (pull_grp hD) hF.base (c_symm hD) ((isGen_iff _).1 hD.w_gen) hG
    (fun _ => 1) (fun _ _ => (_root_.mul_one _).symm) g
  exact ⟨g', (isPullGtF_iff hD hF _ _).2 h⟩

include hF in
theorem pullGt_unique {g : GtPtF D F} {g' g'' : GtPtF D' F} (h : IsPullGtF φ hD F g g') (h' : IsPullGtF φ hD F g g'') :
    g' = g'' :=
  ArcTransport.GtRel.unique (pull_grp hD) hF.base (c_symm hD) ((isGen_iff _).1 hD.w_gen)
    ((isPullGtF_iff hD hF _ _).1 h) ((isPullGtF_iff hD hF _ _).1 h')

theorem pullGt_unique' {g₁ g₂ : GtPtF D F} {g' : GtPtF D' F} (h : IsPullGtF φ hD F g₁ g')
    (h' : IsPullGtF φ hD F g₂ g') : g₁ = g₂ :=
  gt_ext_val (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ y J hJ => by
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    exact (pullGt_val hD h χ (𝟙 _) hJ hJ').trans (pullGt_val hD h' χ (𝟙 _) hJ hJ').symm

def pullGt : GtPtF D F →+ GtPtF D' F :=
  AddMonoidHom.mk' (fun g => (exists_pullGt hD hG hF g).choose) fun g g' => (isAdd_iff_eq _ _ _).1
    (ArcTransport.GtRel.isAdd (pull_grp hD) hF.base (c_symm hD) ((isGen_iff _).1 hD.w_gen) hG
      (fun _ => (_root_.mul_one _).symm) ((isPullGtF_iff hD hF _ _).1 (exists_pullGt hD hG hF g).choose_spec)
      ((isPullGtF_iff hD hF _ _).1 (exists_pullGt hD hG hF g').choose_spec)
      ((isPullGtF_iff hD hF _ _).1 (exists_pullGt hD hG hF (g + g')).choose_spec) ((isAdd_iff_eq _ _ _).2 rfl))

theorem isPullGtF_pullGt (g : GtPtF D F) : IsPullGtF φ hD F g (pullGt hD hG hF g) :=
  (exists_pullGt hD hG hF g).choose_spec

theorem isPullGtF_iff_eq (g : GtPtF D F) (g' : GtPtF D' F) : IsPullGtF φ hD F g g' ↔ g' = pullGt hD hG hF g :=
  ⟨fun h => pullGt_unique hD hF h (isPullGtF_pullGt hD hG hF g), fun h => h ▸ isPullGtF_pullGt hD hG hF g⟩

theorem pullGt_injective : Function.Injective (pullGt hD hG hF) := fun g g' h =>
  pullGt_unique' hD (isPullGtF_pullGt hD hG hF g) (h ▸ isPullGtF_pullGt hD hG hF g')

theorem pullGt_iota (hB : D.TauBimult) (hB' : D'.TauBimult) (x : D'.X) :
    pullGt hD hG hF (iota hB F (hD.xe x)) = iota hB' F x := by
  have h := isPullGtF_pullGt hD hG hF (iota hB F (hD.xe x))
  have hb : (pullGt hD hG hF (iota hB F (hD.xe x))).b = cP D' _ x := by
    refine ArcTransport.pushF_injective (pull_grp hD) hF.base (Over.OverMorphism.ext (h.1.trans ?_))
    rw [iota_b]
    exact ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _) (hF.base.trans (Category.id_comp _).symm) x).trans
      (Category.id_comp _)).symm
  refine gt_ext_val (hb.trans (iota_b _ _).symm) fun χ y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := Sp F) y
  have e := pullGt_val hD h χ (𝟙 _) hJ hJ'
  have e₁ := iota_val hB (F := F) (hD.xe x) (hD.xe χ) hJ
  have e₂ := tau_val hD (Z := Sp F) (𝟙 _ ≫ jFK (R := R) F) (𝟙 _ ≫ jFK (R := R') F) (by
    rw [Category.id_comp, Category.id_comp]; exact hF.sq) hJ hJ' x χ
  have a₁ : ∀ χ, (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ D'.xK χ = 𝟙 (Sp F) ≫ (cP D' (TF (R := R') F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ (1 : TK R' ⟶ D'.P.A).left = 𝟙 (Sp F) ≫ (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (Category.assoc _ _ _).symm)
  rw [a₁, a₁, a₁, a₂, cPoint_add, mul_comm (cP D' _ x), mul_right_comm _ (om _ _ _ _ _) (om _ _ _ _ _)] at e₂
  have e₃ : (om hD.w y J J' (𝟙 (Sp F) ≫ (cP D' _ χ * (pullGt hD hG hF (iota hB F (hD.xe x))).b).left))⁻¹ *
      om hD.w y J J' (𝟙 (Sp F) ≫ (cP D' (TF (R := R') F) χ).left) *
      om hD.w y J J' (𝟙 (Sp F) ≫ (pullGt hD hG hF (iota hB F (hD.xe x))).b.left) =
      (om hD.w y J J' (𝟙 (Sp F) ≫ (cP D' (TF (R := R') F) χ * cP D' _ x).left))⁻¹ *
      om hD.w y J J' (𝟙 (Sp F) ≫ (cP D' (TF (R := R') F) χ).left) *
      om hD.w y J J' (𝟙 (Sp F) ≫ (cP D' (TF (R := R') F) x).left) := by rw [hb]
  rw [e₃] at e
  exact (mul_left_cancel (e.symm.trans (e₁.trans e₂))).trans (iota_val hB' x χ hJ').symm

section Action

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] {oa : D.OAct O} {oa' : D'.OAct O}
  (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
  (ho : ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)

include hx ho in
theorem pullGt_gtSmul (a : O) (g : GtPtF D F) :
    pullGt hD hG hF (gtSmul hG oa a g) = gtSmul hG oa' a (pullGt hD hG hF g) := by
  have h := isPullGtF_pullGt hD hG hF g
  set g' := pullGt hD hG hF g
  have := oa'.onB.hom a
  have := oa'.onB.hom (star a)
  refine ((isPullGtF_iff_eq hD hG hF _ _).1 (isPullGtF_of_val hD hF ?_ fun χ y J J' hJ hJ' => ?_)).symm
  · rw [gtSmul_b, gtSmul_b, Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc]
    exact congrArg (· ≫ _) h.1
  · let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk y)ˣ := fun x => om hD.w y J J' x.left
    let V : ((Sp F).presheaf.stalk y)ˣ := val₂ (rosGen hG oa a) (T := TF (R := R) F) y J (cP D _ (hD.xe χ)) g.b
    let V' : ((Sp F).presheaf.stalk y)ˣ := val₂ (rosGen hG oa' a) (T := TF (R := R') F) y J' (cP D' _ χ) g'.b
    have e₁ : vS ((gtSmul hG oa a g).s (hD.xe χ)) y J = vS (g.s (star a • hD.xe χ)) y J * V :=
      gtSmul_val hG oa a g (hD.xe χ) hJ
    have e₂ : vS ((gtSmul hG oa' a g').s χ) y J' = vS (g'.s (star a • χ)) y J' * V' := gtSmul_val hG oa' a g' χ hJ'
    have e₃ := pullGt_val hD h (star a • χ) (𝟙 _) hJ hJ'
    have e₄ : V = Ω ((cP D' _ χ ≫ oa'.onB.act (star a)) * g'.b) * (Ω (cP D' _ χ ≫ oa'.onB.act (star a)))⁻¹ *
        (Ω g'.b)⁻¹ * (Ω (cP D' _ χ * (g'.b ≫ oa'.onB.act a)))⁻¹ * Ω (cP D' _ χ) * Ω (g'.b ≫ oa'.onB.act a) * V' :=
      ros_val hG (pull_grp hD) D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho (star a)) (ho a)
      (rosGen_isRos hG oa a) (rosGen_isRos hG oa' a) (cP D' (TF (R := R') F) χ) g'.b
      (lift (cP D (TF (R := R) F) (hD.xe χ)) g.b).left
      (((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _) (hF.base.trans (Category.id_comp _).symm) χ).trans
        (Category.id_comp _)).trans (congrArg (fun q => q.left) (lift_fst (cP D (TF (R := R) F) (hD.xe χ)) g.b).symm))
      (h.1.trans (congrArg (fun q => q.left) (lift_snd (cP D (TF (R := R) F) (hD.xe χ)) g.b).symm)) hJ hJ'
    simp only [Category.id_comp] at e₃
    have e₅ : vS (g.s (hD.xe (star a • χ))) y J = (Ω (cP D' _ (star a • χ) * g'.b))⁻¹ * Ω (cP D' _ (star a • χ)) *
        Ω g'.b * (Ω 1)⁻¹ * vS (g'.s (star a • χ)) y J' := e₃
    rw [hx, cPoint_smul oa'] at e₅
    show _ = (Ω (cP D' _ χ * (gtSmul hG oa' a g').b))⁻¹ * Ω (cP D' _ χ) * Ω (gtSmul hG oa' a g').b * (Ω 1)⁻¹ * _
    rw [e₁, e₂, e₅, e₄, gtSmul_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Action

section Qk

variable (hB : D.TauBimult) (hB' : D'.TauBimult) {k : ℕ}

def pullQk (p : QkPt D F k) : QkPt D' F k :=
  qkMk hB' (hD.xe.symm p.y) (pullGt hD hG hF p.g) (by
    rw [← map_nsmul, qk_nsmul hB, ← pullGt_iota hD hG hF hB hB', AddEquiv.apply_symm_apply])

theorem pullQk_y (p : QkPt D F k) : (pullQk hD hG hF hB hB' p).y = hD.xe.symm p.y := rfl

theorem pullQk_g (p : QkPt D F k) : (pullQk hD hG hF hB hB' p).g = pullGt hD hG hF p.g := rfl

theorem eq_pullQk_iff (p : QkPt D F k) (p' : QkPt D' F k) :
    p' = pullQk hD hG hF hB hB' p ↔ p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g :=
  ⟨fun h => h ▸ ⟨rfl, isPullGtF_pullGt hD hG hF _⟩, fun h => qk_ext h.1 ((isPullGtF_iff_eq hD hG hF _ _).1 h.2)⟩

theorem pullQk_surjective : Function.Surjective (pullQk hD hG hF hB hB' (k := k)) := fun p' => by
  obtain ⟨p, h⟩ := qkPullExists hG R R' φ D D' hD F hF k p'
  exact ⟨p, ((eq_pullQk_iff hD hG hF hB hB' p p').2 h).symm⟩

theorem equiv_pullQk (p q : QkPt D F k) :
    QkPt.Equiv D' F (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) ↔ QkPt.Equiv D F p q := by
  rw [equiv_iff hB, equiv_iff hB', hD.xe.surjective.exists]
  refine exists_congr fun z => and_congr ?_ ?_
  · rw [pullQk_y, pullQk_y, ← hD.xe.symm.injective.eq_iff, map_add, map_nsmul, AddEquiv.symm_apply_apply]
  · rw [pullQk_g, pullQk_g, ← pullGt_iota hD hG hF hB hB', ← map_add, (pullGt_injective hD hG hF).eq_iff]

theorem qkAdd_pullQk {p q r : QkPt D F k} (h : QkAdd p q r) :
    QkAdd (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) (pullQk hD hG hF hB hB' r) := by
  have e : qkAdd hB' (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) = pullQk hD hG hF hB hB' (qkAdd hB p q) :=
    qk_ext (map_add hD.xe.symm _ _).symm (map_add (pullGt hD hG hF) _ _).symm
  rw [qkAdd_iff hB', e, equiv_pullQk]
  exact (qkAdd_iff hB _ _ _).1 h

theorem qkAct_pullQk {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] {oa : D.OAct O}
    {oa' : D'.OAct O} (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
    (ho : ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left) {a : O} {p r : QkPt D F k}
    (h : QkAct oa a p r) : QkAct oa' a (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' r) := by
  have e : qkSmul hB' hG oa' a (pullQk hD hG hF hB hB' p) = pullQk hD hG hF hB hB' (qkSmul hB hG oa a p) :=
    qk_ext (hD.xe.injective (by
      show hD.xe (a • hD.xe.symm p.y) = hD.xe (hD.xe.symm (a • p.y))
      rw [hx, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])) (pullGt_gtSmul hD hG hF hx ho a p.g).symm
  rw [qkAct_iff hB' hG, e, equiv_pullQk]
  exact (qkAct_iff hB hG oa _ _ _).1 h

theorem isNsmul_pullGt {m : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul m g h) :
    GtPtF.IsNsmul m (pullGt hD hG hF g) (pullGt hD hG hF h) := by
  rw [isNsmul_iff_eq] at H ⊢
  rw [H, map_nsmul]

end Qk

theorem isPullGtF_ext {F' : Type} [Field F'] [Algebra (FractionRing R) F'] [Algebra (FractionRing R') F']
    (hF' : Compat φ F') (f : F →+* F') (hf' : f.comp (algebraMap (FractionRing R') F) = algebraMap (FractionRing R') F')
    {k : ℕ} {p : QkPt D F k} {p' : QkPt D' F k} {q : QkPt D F' k} {q' : QkPt D' F' k} (h : IsPullGtF φ hD F p.g p'.g)
    (hq : QkExt f p q) (hq' : QkExt f p' q') : IsPullGtF φ hD F' q.g q'.g := by
  refine isPullGtF_of_val hD hF' ?_ fun χ y J J' hJ hJ' => ?_
  · rw [hq'.2.1, hq.2.1, Category.assoc]
    exact congrArg (_ ≫ ·) h.1
  · have e := pullGt_val hD h χ (spMap f) hJ hJ'
    have e₁ := (val_corr hJ (hq.2.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
    have e₂ := (val_corr hJ' (hq'.2.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    rw [Category.id_comp] at e₁ e₂
    have b : q'.g.b = extMap f hf' ≫ p'.g.b := Over.OverMorphism.ext hq'.2.1
    have a₁ : (cP D' _ χ * q'.g.b).left = spMap f ≫ (cP D' _ χ * p'.g.b).left := by
      rw [b, ← comp_cP D' (extMap f hf'), ← MonObj.comp_mul]; rfl
    have a₂ : (cP D' (TF (R := R') F') χ).left = spMap f ≫ (cP D' (TF (R := R') F) χ).left := by
      rw [← comp_cP D' (extMap f hf')]; rfl
    have a₃ : (1 : TF (R := R') F' ⟶ D'.P.A).left = spMap f ≫ (1 : TF (R := R') F ⟶ D'.P.A).left := by
      rw [← MonObj.comp_one (extMap f hf')]; rfl
    refine e₁.trans (e.trans (congrArg₂ (· * ·) ?_ e₂.symm))
    rw [a₁, a₂, a₃, hq'.2.1]

end GlobalTheory.ArcPull
