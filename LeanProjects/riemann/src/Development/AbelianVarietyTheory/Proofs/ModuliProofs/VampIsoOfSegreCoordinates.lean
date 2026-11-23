import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.SegreSquare
open GlobalTheory.SegreCoord

variable {X Y : Scheme.{0}} {σ τ : Type}

theorem isUnit_of_mem {M : LB X} (s : M.Sec) (f : Y ⟶ X) (y : Y) (h : f y ∈ Out.nonzeroLocus s) {j : M.ι}
    (hj : f y ∈ M.U j) : IsUnit (gs f y _ (s.f j)) := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus s _).1 h
  rw [gs_sec s f y hj hk, Geo.Tor.gs_stalkMap f y _ hk]
  exact (Units.isUnit _).mul (u.map _)

theorem mem_of_isUnit {M : LB X} (s : M.Sec) (f : Y ⟶ X) (y : Y) {j : M.ι}
    (hj : f y ∈ M.U j) (h : IsUnit (gs f y _ (s.f j))) : f y ∈ Out.nonzeroLocus s := by
  rw [Geo.Tor.gs_stalkMap f y _ hj] at h
  exact (mem_nonzeroLocus s _).2 ⟨j, hj, (isUnit_map_iff (f.stalkMap y).hom _).1 h⟩

theorem lbIso_of_proportional {A B : LB Y} (a : τ → A.Sec) (b : τ → B.Sec) (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤)
    (h : ∀ (y : Y) (l : A.ι) (m : B.ι), y ∈ A.U l → y ∈ B.U m → ∃ u : (Y.presheaf.stalk y)ˣ,
      ∀ i, gs (𝟙 Y) y _ ((b i).f m) = u * gs (𝟙 Y) y _ ((a i).f l)) : LBIso A B := by
  have pt : ∀ y : Y, ∃ i, y ∈ Out.nonzeroLocus (a i) := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, Out.nonzeroLocus (a i) by rw [hc]; trivial)
  have key : ∀ (m : B.ι) (l : A.ι), ∃ w : Γ(Y, B.U m ⊓ A.U l)ˣ, ∀ y ∈ B.U m ⊓ A.U l, ∀ i,
      gs (𝟙 Y) y _ ((b i).f m) = (gm (𝟙 Y) y _ w).val * gs (𝟙 Y) y _ ((a i).f l) := by
    intro m l
    let W : τ → Y.Opens := fun i => B.U m ⊓ A.U l ⊓ Out.nonzeroLocus (a i)
    have lA : ∀ i, W i ≤ A.U l := fun i => inf_le_left.trans inf_le_right
    have lB : ∀ i, W i ≤ B.U m := fun i => inf_le_left.trans inf_le_left
    have ua : ∀ i, IsUnit (resG Y (lA i) ((a i).f l)) := fun i =>
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (gs_res (𝟙 Y) y (lA i) hy _))).mpr
          (isUnit_of_mem (a i) (𝟙 Y) y hy.2 hy.1.2)
    have ub : ∀ i, IsUnit (resG Y (lB i) ((b i).f m)) := fun i =>
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (gs_res (𝟙 Y) y (lB i) hy _))).mpr (by
          obtain ⟨u, hu⟩ := h y l m hy.1.2 hy.1.1
          rw [hu]
          exact u.isUnit.mul (isUnit_of_mem (a i) (𝟙 Y) y hy.2 hy.1.2))
    have val : ∀ i y (hy : y ∈ W i) (u : (Y.presheaf.stalk y)ˣ),
        (∀ i, gs (𝟙 Y) y _ ((b i).f m) = u * gs (𝟙 Y) y _ ((a i).f l)) →
        gm (𝟙 Y) y (W i) ((ub i).unit * (ua i).unit⁻¹) = u := fun i y hy u hu => by
      rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [Units.val_mul, ← gs_unit _ y _ hy, ← gs_unit _ y _ hy, IsUnit.unit_spec, IsUnit.unit_spec,
        gs_res (𝟙 Y) y (lA i) hy, gs_res (𝟙 Y) y (lB i) hy, hu]
    obtain ⟨w, hw⟩ := glue_unit (B.U m ⊓ A.U l) W (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨i, hi⟩ := pt y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩) (fun i => (ub i).unit * (ua i).unit⁻¹) (fun i j y hy => by
      obtain ⟨u, hu⟩ := h y l m hy.1.1.2 hy.1.1.1
      rw [val i y hy.1 u hu, val j y hy.2 u hu])
    refine ⟨w, fun y hy i => ?_⟩
    obtain ⟨u, hu⟩ := h y l m hy.2 hy.1
    obtain ⟨k, hk⟩ := pt y
    have hy' : y ∈ W k := ⟨hy, hk⟩
    rw [← gm_res (𝟙 Y) y (inf_le_left : W k ≤ _) hy', hw, val k y hy' u hu, hu]
  choose w hw using key
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ?_).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y p q hy)
    (gm_res _ y _ hy _))).symm
  obtain ⟨i, hi⟩ := pt y
  have e₁ := hw p.1 p.2 y hy.1 i
  have e₂ := hw q.1 q.2 y hy.2 i
  rw [gs_sec (b i) (𝟙 Y) y hy.1.1 hy.2.1, gs_sec (a i) (𝟙 Y) y hy.1.2 hy.2.2, e₂, ← mul_assoc, ← mul_assoc] at e₁
  have e₃ := (isUnit_of_mem (a i) (𝟙 Y) y hi hy.2.2).mul_right_cancel e₁
  rw [← Units.val_mul, ← Units.val_mul, Units.val_inj] at e₃
  rw [mul_right_comm]
  exact eq_mul_inv_of_mul_eq e₃.symm

variable {M : LB X} {th : σ → M.Sec} {p q : Y ⟶ X} {M₂ : LB Y} {th₂ : σ × σ → M₂.Sec}

theorem germ_eq (hM : M.IsLB)
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Y) (v₁ v₂ : σ → T), SecCoord M th (x ≫ p) v₁ → SecCoord M th (x ≫ q) v₂ →
      SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2))
    (y : Y) {j k : M.ι} {l : M₂.ι} (hj : p y ∈ M.U j) (hk : q y ∈ M.U k) (hl : y ∈ M₂.U l) :
    ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i : σ × σ,
      gs p y _ ((th i.1).f j) * gs q y _ ((th i.2).f k) = u * gs (𝟙 Y) y _ ((th₂ i).f l) := by
  obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := p ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ M.U k) (x := y) ⟨hj, hk⟩
  let x : Sp Γ(Y, W) ⟶ Y := hW.fromSpec
  have hx : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  have hr : Set.range x = W := hW.range_fromSpec
  obtain ⟨z, rfl⟩ : y ∈ Set.range x := hr ▸ hy
  have hin : ∀ z, x z ∈ W := fun z => hr.le ⟨z, rfl⟩
  obtain ⟨v₁, h₁⟩ := exists_secCoord (th := th) (x := x ≫ p) hM (k := j) fun z => (hle (hin z)).1
  obtain ⟨v₂, h₂⟩ := exists_secCoord (th := th) (x := x ≫ q) hM (k := k) fun z => (hle (hin z)).2
  obtain ⟨u, hu⟩ := loc_of_secCoord (H _ x v₁ v₂ h₁ h₂) z l hl
  obtain ⟨u₁, hu₁⟩ := loc_of_secCoord h₁ z j hj
  obtain ⟨u₂, hu₂⟩ := loc_of_secCoord h₂ z k hk
  let e := (asIso (x.stalkMap z)).commRingCatIsoToRingEquiv
  refine ⟨Units.map e.symm.toMonoidHom (u₁ * u₂ * u⁻¹), fun i => e.injective ?_⟩
  rw [map_mul, map_mul]
  have a₁ : e (gs p (x z) _ ((th i.1).f j)) = _ := (SegreCoord.gs_stalkMap x p z _ hj _).symm.trans (hu₁ i.1)
  have a₂ : e (gs q (x z) _ ((th i.2).f k)) = _ := (SegreCoord.gs_stalkMap x q z _ hk _).symm.trans (hu₂ i.2)
  have a₃ : e (gs (𝟙 Y) (x z) _ ((th₂ i).f l)) = _ := (Geo.Tor.gs_stalkMap x z _ hl _).symm.trans (hu i)
  have a₄ : e (Units.map e.symm.toMonoidHom (u₁ * u₂ * u⁻¹)).val = (u₁ * u₂ * u⁻¹).val := e.apply_symm_apply _
  rw [a₁, a₂, a₃, a₄, map_mul, Units.val_mul, Units.val_mul]
  linear_combination (-(ev z (v₁ i.1) * ev z (v₂ i.2) * u₁.val * u₂.val)) * u.inv_mul

section
variable (hM : M.IsLB) (hM₂ : M₂.IsLB)
  (G : ∀ (y : Y) {j k : M.ι} {l : M₂.ι}, p y ∈ M.U j → q y ∈ M.U k → y ∈ M₂.U l →
    ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i : σ × σ,
      gs p y _ ((th i.1).f j) * gs q y _ ((th i.2).f k) = u * gs (𝟙 Y) y _ ((th₂ i).f l))
include hM hM₂ G

theorem locus_eq (i : σ × σ) : Out.nonzeroLocus (th₂ i) =
    p ⁻¹ᵁ Out.nonzeroLocus (th i.1) ⊓ q ⁻¹ᵁ Out.nonzeroLocus (th i.2) := by
  ext y
  obtain ⟨j, hj⟩ := exists_chart hM (p y)
  obtain ⟨k, hk⟩ := exists_chart hM (q y)
  obtain ⟨l, hl⟩ := exists_chart hM₂ y
  obtain ⟨u, hu⟩ := G y hj hk hl
  constructor
  · intro h
    have := u.isUnit.mul (isUnit_of_mem (th₂ i) (𝟙 Y) y h hl)
    rw [← hu] at this
    exact ⟨mem_of_isUnit _ p y hj (isUnit_of_mul_isUnit_left this), mem_of_isUnit _ q y hk (isUnit_of_mul_isUnit_right this)⟩
  · intro h
    have := (isUnit_of_mem (th i.1) p y h.1 hj).mul (isUnit_of_mem (th i.2) q y h.2 hk)
    rw [hu] at this
    exact mem_of_isUnit (th₂ i) (𝟙 Y) y hl (isUnit_of_mul_isUnit_right this)

omit hM₂ in
theorem sec_congr (i i' : σ × σ) (h₁ : ∀ j, (th i.1).f j = (th i'.1).f j) (h₂ : ∀ j, (th i.2).f j = (th i'.2).f j)
    (l : M₂.ι) : (th₂ i).f l = (th₂ i').f l := fn_ext fun y hl => by
  obtain ⟨j, hj⟩ := exists_chart hM (p y)
  obtain ⟨k, hk⟩ := exists_chart hM (q y)
  obtain ⟨u, hu⟩ := G y hj hk hl
  exact u.isUnit.mul_left_cancel ((hu i).symm.trans (by rw [h₁, h₂, hu i']))

theorem cover (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) : ⨆ i, Out.nonzeroLocus (th₂ i) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p y ∈ ⨆ i, Out.nonzeroLocus (th i) by rw [hc]; trivial)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show q y ∈ ⨆ i, Out.nonzeroLocus (th i) by rw [hc]; trivial)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ?_⟩
  rw [locus_eq hM hM₂ G]
  exact ⟨hi, hj⟩

theorem iso_box (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) : LBIso M₂ (boxLB M p q) :=
  lbIso_of_proportional th₂ (boxTh th p q) (cover hM hM₂ G hc) fun y l m hl hm => by
    obtain ⟨u, hu⟩ := G y (LB.wchart_le M ![p, q] m 0 hm) (LB.wchart_le M ![p, q] m 1 hm) hl
    refine ⟨u, fun i => (gs_boxF p q _ _ m (𝟙 Y) y hm).trans ?_⟩
    rw [Category.id_comp, Category.id_comp]
    exact hu i

omit hM₂ G in
theorem gs_ratio {i : σ} {r : σ → Γ(X, Out.nonzeroLocus (th i))}
    (hr : ∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) :
    (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : σ) {k : M.ι}, f y ∈ Out.nonzeroLocus (th i) → f y ∈ M.U k →
      gs f y _ ((th j).f k) = gs f y _ (r j) * gs f y _ ((th i).f k)) ∧ r i = 1 := by
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : σ) {k : M.ι}, f y ∈ Out.nonzeroLocus (th i) → f y ∈ M.U k →
      gs f y _ ((th j).f k) = gs f y _ (r j) * gs f y _ ((th i).f k) := fun f y j k h hk => by
    have hm : f y ∈ Out.nonzeroLocus (th i) ⊓ M.U k := ⟨h, hk⟩
    have e := congrArg (gs f y _) (hr j k)
    rwa [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  refine ⟨key, fn_ext fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM y
  refine (isUnit_of_mem (th i) (𝟙 X) y hy hk).mul_right_cancel ((key (𝟙 X) y i hy hk).symm.trans ?_)
  rw [gs_eq (𝟙 X) y _ hy 1, map_one, map_one, one_mul]

theorem vamp {K : Type} [Field K] {s : X ⟶ Sp K} (sq : IsPullback p q s s) (hV : VAmp s M th) :
    VAmp (p ≫ s) M₂ th₂ := by
  refine ⟨cover hM hM₂ G hV.1, fun a => ?_⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hV.2 a.1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := hV.2 a.2
  obtain ⟨g₁, o₁⟩ := gs_ratio hM hr₁
  obtain ⟨g₂, o₂⟩ := gs_ratio hM hr₂
  have loc := locus_eq hM hM₂ G a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => (p.appLE _ _ l₁).hom (r₁ b.1) * (q.appLE _ _ l₂).hom (r₂ b.2), fun b l => fn_ext fun y hy => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of K))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · obtain ⟨j, hj⟩ := exists_chart hM (p y)
    obtain ⟨k, hk⟩ := exists_chart hM (q y)
    obtain ⟨u, hu⟩ := G y hj hk hy.2
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_mul _ y _ hy.1,
      SegreCoord.gs_appLE p y l₁ hy.1, SegreCoord.gs_appLE q y l₂ hy.1]
    refine u.isUnit.mul_left_cancel ?_
    rw [← hu b, mul_left_comm, ← hu a, g₁ p y b.1 (l₁ hy.1) hj, g₂ q y b.2 (l₂ hy.1) hk, mul_mul_mul_comm]
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    let φ := MvPolynomial.eval₂Hom (RingHom.comp ((p ≫ s).appLE ⊤ (Out.nonzeroLocus (th₂ a)) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      (fun b : σ × σ => (p.appLE _ _ l₁).hom (r₁ b.1) * (q.appLE _ _ l₂).hom (r₂ b.2))
    suffices h : φ.range = ⊤ by
      intro f
      obtain ⟨F, hF⟩ := (RingHom.range_eq_top.1 h) f
      exact ⟨F, hF.symm⟩
    rw [← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change (p.appLE _ _ l₁).hom _ ∈ φ.range
      induction F using MvPolynomial.induction_on with
      | C c =>
        refine ⟨MvPolynomial.C c, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C, RingHom.comp_apply, RingHom.comp_apply]
        exact (RepBC.appLE_appLE p s _ _ _ _).symm
      | add F G hF hG => rw [MvPolynomial.eval₂_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [MvPolynomial.eval₂_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (i, a.2), ?_⟩
        simp only [φ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂_X, o₂, map_one, mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change (q.appLE _ _ l₂).hom _ ∈ φ.range
      induction F using MvPolynomial.induction_on with
      | C c =>
        refine ⟨MvPolynomial.C c, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C, sq.w, RingHom.comp_apply, RingHom.comp_apply]
        exact (RepBC.appLE_appLE q s _ _ _ _).symm
      | add F G hF hG => rw [MvPolynomial.eval₂_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [MvPolynomial.eval₂_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (a.1, i), ?_⟩
        simp only [φ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂_X, o₁, map_one, one_mul]

end

theorem vamp_iso_of_segre_coordinates : ∀ (K σ : Type) [Field K] [Finite σ] (Z : Over (Sp K)) (M : LB Z.left) (th : σ → M.Sec) (M₂ : LB (Z ⊗ Z).left) (th₂ : σ × σ → M₂.Sec), M.IsLB → M₂.IsLB → VAmp Z.hom M th → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : σ → T), SecCoord M th (x ≫ (fst Z Z).left) v₁ → SecCoord M th (x ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → VAmp (Z ⊗ Z).hom M₂ th₂ ∧ LBIso M₂ (LB.LinComb M (K := Fin 2) ![(fst Z Z).left, (snd Z Z).left] ![1, 1]) ∧ ∀ i i' : σ × σ, (∀ j, (th i.1).f j = (th i'.1).f j) → (∀ j, (th i.2).f j = (th i'.2).f j) → ∀ j, (th₂ i).f j = (th₂ i').f j := by
  intro K σ _ _ Z M th M₂ th₂ hM hM₂ hV H
  have hP : IsPullback (fst Z Z).left (snd Z Z).left Z.hom Z.hom := IsPullback.of_hasPullback Z.hom Z.hom
  have G := @germ_eq _ _ _ _ _ _ _ _ _ hM H
  refine ⟨?_, ?_, sec_congr hM G⟩
  · rw [← Over.w (fst Z Z)]
    exact vamp hM hM₂ G hP hV
  · rw [show (![1, 1] : Fin 2 → ℤ) = fun _ => 1 from funext fun i => by fin_cases i <;> rfl]
    exact iso_box hM hM₂ G hV.1

end GlobalTheory.ZV.SegreSquare
end
