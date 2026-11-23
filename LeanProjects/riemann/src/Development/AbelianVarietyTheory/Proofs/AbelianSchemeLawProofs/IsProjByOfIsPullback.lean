import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]

def ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* Γ(P, W) :=
  (p.appLE U W h).hom

theorem rs_ap (p : P ⟶ X) {U : X.Opens} {W W' : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W' ≤ W) (x : Γ(X, U)) :
    rs P h' (ap p h x) = ap p (h'.trans h) x :=
  congr($(p.appLE_map h (homOfLE h').op).hom x)

theorem ap_rs (p : P ⟶ X) {U U' : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U') (h' : U' ≤ U) (x : Γ(X, U)) :
    ap p h (rs X h' x) = ap p (h.trans fun _ hy => h' hy) x :=
  congr($(p.map_appLE h (homOfLE h').op).hom x)

theorem basicOpen_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (x : Γ(X, U)) :
    P.basicOpen (ap p h x) = W ⊓ p ⁻¹ᵁ X.basicOpen x :=
  Scheme.basicOpen_appLE p W U h x

theorem ap_cst (p : P ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {W : P.Opens}
    (h : W ≤ p ⁻¹ᵁ U) (r : R) : ap p h (cst f U r) = cst (p ≫ f) W r := by
  refine (ap_rs p h le_top _).trans ?_
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rs X h u.val := rfl

theorem le_pre (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W ≤ p ⁻¹ᵁ V) :
    W ≤ p ⁻¹ᵁ (U ⊓ V) := fun _ hy => ⟨h hy, h' hy⟩

theorem pre_left (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ U := fun _ hy => (h hy).1

theorem pre_right (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ V := fun _ hy => (h hy).2

def box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) : LB P :=
  ⟨H.ι × K.ι, fun a => p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2, fun a b =>
    Units.map (ap p (le_pre p (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).toMonoidHom
      (H.g a.1 b.1) *
    Units.map (ap q (le_pre q (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).toMonoidHom
      (K.g a.2 b.2)⟩

variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem rs_mul {U : X.Opens} {V : Y.Opens} {W W' : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V)
    (h : W' ≤ W) (x : Γ(X, U)) (y : Γ(Y, V)) :
    rs P h (ap p h₁ x * ap q h₂ y) = ap p (h.trans h₁) x * ap q (h.trans h₂) y := by
  rw [map_mul, rs_ap, rs_ap]

theorem ap_g_self (hH : H.IsLB) (i : H.ι) {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U i)) :
    ap p h (H.g i i).val = 1 := by
  have h₁ := congrArg (fun u => ap p (pre_left p h) u.val) (hH.g_self i)
  simpa only [val_res, ap_rs, Units.val_one, map_one] using h₁

theorem ap_cocycle (hH : H.IsLB) (i j k : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j))
    (h₂ : W ≤ p ⁻¹ᵁ (H.U j ⊓ H.U k)) (h₃ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U k)) :
    ap p h₃ (H.g i k).val = ap p h₁ (H.g i j).val * ap p h₂ (H.g j k).val := by
  have e := congrArg (fun u => ap p (le_pre p h₁ (pre_right p h₂)) u.val) (hH.cocycle i j k)
  simp only [val_res, ap_rs, Units.val_mul, map_mul] at e
  exact e.symm

theorem ap_ratio {U V : X.Opens} {x y : Γ(X, V)} {r : Γ(X, U)}
    (e : rs X (inf_le_right : U ⊓ V ≤ V) x =
      rs X (inf_le_left : U ⊓ V ≤ U) r * rs X (inf_le_right : U ⊓ V ≤ V) y)
    {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ p ⁻¹ᵁ V) :
    ap p h₂ x = ap p h₁ r * ap p h₂ y := by
  have e' := congrArg (ap p (le_pre p h₁ h₂)) e
  simpa only [ap_rs, map_mul] using e'

theorem ap_compat (s : LB.Sec H) (i j : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ H.U i) (h₂ : W ≤ p ⁻¹ᵁ H.U j)
    (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j)) :
    ap p h₁ (s.f i) = ap p h (H.g i j).val * ap p h₂ (s.f j) := by
  have e : rs X inf_le_left (s.f i) = (H.g i j).val * rs X inf_le_right (s.f j) := s.compat i j
  have e' := congrArg (ap p h) e
  simpa only [ap_rs, map_mul] using e'

theorem isLB_box (hH : H.IsLB) (hK : K.IsLB) : (box p q H K).IsLB where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, K.U i by rw [hK.cover]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  g_self := fun a => by
    refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
    rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
  cocycle := fun a b c => by
    refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
      (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
    exact (mul_mul_mul_comm _ _ _ _).trans
      (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)

def boxSec (s : LB.Sec H) (t : LB.Sec K) : LB.Sec (box p q H K) where
  f := fun a => ap p (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_left (s.f a.1) *
    ap q (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_right (t.f a.2)
  compat := fun a b => by
    refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (rs_mul p q _ _ _ _ _).symm))
    exact (congrArg₂ (· * ·) (ap_compat p s a.1 b.1 _ _ _) (ap_compat q t a.2 b.2 _ _ _)).trans
      (mul_mul_mul_comm _ _ _ _)

theorem nonzeroLocus_boxSec (s : LB.Sec H) (t : LB.Sec K) :
    nonzeroLocus (boxSec p q s t) = p ⁻¹ᵁ nonzeroLocus s ⊓ q ⁻¹ᵁ nonzeroLocus t := by
  have key : ∀ a : H.ι × K.ι, P.basicOpen ((boxSec p q s t).f a) =
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ p ⁻¹ᵁ X.basicOpen (s.f a.1)) ⊓
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ q ⁻¹ᵁ Y.basicOpen (t.f a.2)) := fun a =>
    (P.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (basicOpen_ap p _ _) (basicOpen_ap q _ _))
  ext y
  constructor
  · intro h
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have ha := (key a).le ha
    exact ⟨TopologicalSpace.Opens.mem_iSup.2 ⟨a.1, ha.1.2⟩, TopologicalSpace.Opens.mem_iSup.2 ⟨a.2, ha.2.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ k, X.basicOpen (s.f k) from h₁)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ k, Y.basicOpen (t.f k) from h₂)
    have hy : y ∈ p ⁻¹ᵁ H.U i ⊓ q ⁻¹ᵁ K.U j := ⟨X.basicOpen_le _ hi, Y.basicOpen_le _ hj⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (key (i, j)).ge ⟨⟨hy, hi⟩, hy, hj⟩⟩

theorem ratio_self (s : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) : r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k => X.basicOpen (s.f k)) (nonzeroLocus s)
    (fun k => homOfLE (le_iSup (fun k => X.basicOpen (s.f k)) k)) le_rfl r 1 fun k => ?_
  have hle : X.basicOpen (s.f k) ≤ nonzeroLocus s ⊓ H.U k :=
    le_inf (le_iSup (fun k => X.basicOpen (s.f k)) k) (X.basicOpen_le _)
  have e := congrArg (rs X hle) (h k)
  simp only [map_mul, rs_rs] at e
  have u : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) := X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  have e' : rs X (hle.trans inf_le_left) r = 1 := u.mul_right_cancel (e.symm.trans (_root_.one_mul _).symm)
  exact e'.trans (map_one (rs X (hle.trans inf_le_left))).symm

theorem isProjBy_of_isPullback {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (sq : IsPullback p q f g) (hf : IsProjBy f) (hg : IsProjBy g) : IsProjBy (p ≫ f) := by
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  obtain ⟨K, hK, n, t, ht, ht'⟩ := hg
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨box p q H K, isLB_box p q hH hK, m * n + m + n,
    fun a => boxSec p q (s (e a).1) (t (e a).2), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

end GlobalTheory.AbLaw.Segre

theorem GlobalTheory.AbLaw.isProjBy_tensor : ∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))),
    IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom := fun _ _ X Y hX hY =>
  GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback _ _ (IsPullback.of_hasPullback X.hom Y.hom) hX hY
