import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.Ratio

section General

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
  [IsCommMonObj B₁] [GrpObj B']

def tr (M : LB B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z)
    (J J₀ : (Z ⟶ B.left) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ I : ULift.{0} (Finset (Fin 2)), (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))
    ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))

omit [GrpObj B'] in
theorem mem_chart {M : LB B.left} (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z}
    {J : (Z ⟶ B.left) → M.ι} (hJ : Good M z J) :
    β₂ (p z) ∈ (abelian₂ B M).U (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) :=
  Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)

omit [GrpObj B'] in
theorem gm_lam {M : LB B.left} (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z}
    {J J₀ : (Z ⟶ B.left) → M.ι} (hJ : Good M z J) (hJ₀ : Good M z J₀) :
    gm (p ≫ β₂) z _ ((abelian₂ B M).g (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))
      (fun I => J₀ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))) = tr M β₂ p z J J₀ :=
  (gm_linComb M _ _ (p ≫ β₂) z _ _ (mem_chart β₂ p hJ) (mem_chart β₂ p hJ₀)).trans
    (Finset.prod_congr rfl fun I _ => congrArg (· ^ _) (congrArg (fun q => gm ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left) z
      (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q))) (Category.assoc _ _ _).symm))

theorem isoVal_trans {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} {w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')} (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z} {J J₀ : (Z ⟶ B₁.left) → M₁.ι} {J' J₀' : (Z ⟶ B.left) → M.ι}
    (hJ : Good M₁ z J) (hJ₀ : Good M₁ z J₀) (hJ' : Good M z J') (hJ₀' : Good M z J₀') :
    isoVal w p z J J' = tr M₁ β₂' p z J J₀ * (tr M β₂ p z J' J₀')⁻¹ * isoVal w p z J₀ J₀' := by
  have m := mem_chart β₂ p hJ'
  have m₀ := mem_chart β₂ p hJ₀'
  have h := (isGen_iff w).1 hw Z p z _ _ (fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))
    (fun _ I => J₀' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) (mem_chart β₂' p hJ) (mem_chart β₂' p hJ₀)
    (mem_pull.2 m) (mem_pull.2 m₀)
  refine h.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_lam β₂' p hJ hJ₀) (congrArg (·⁻¹) ?_)) rfl)
  refine (gm_linComb (abelian₂ B M) (K := PUnit) (fun _ => β₂) (fun _ => 1) p z _ _ (mem_pull.2 m) (mem_pull.2 m₀)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  exact gm_lam β₂ p hJ' hJ₀'

omit [GrpObj B] [IsCommMonObj B] [GrpObj B'] in
theorem lift_sq {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) {T : Over S'}
    (x y : T ⟶ B') {g : T.left ⟶ S} (x₀ y₀ : Over.mk g ⟶ B) (hx : x₀.left = x.left ≫ β) (hy : y₀.left = y.left ≫ β) :
    (lift x y).left ≫ β₂ = (lift x₀ y₀).left := by
  have e₁ : (lift x y).left ≫ (fst B' B').left = x.left := congrArg (·.left) (lift_fst x y)
  have e₂ : (lift x y).left ≫ (snd B' B').left = y.left := congrArg (·.left) (lift_snd x y)
  have e₃ : (lift x₀ y₀).left ≫ (fst B B).left = x₀.left := congrArg (·.left) (lift_fst x₀ y₀)
  have e₄ : (lift x₀ y₀).left ≫ (snd B B).left = y₀.left := congrArg (·.left) (lift_snd x₀ y₀)
  refine pullback.hom_ext (f := B.hom) (g := B.hom) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hs.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) e₁).trans (hx.symm.trans e₃.symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hs.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) e₂).trans (hy.symm.trans e₄.symm))))

omit [GrpObj B'] in

theorem val_trans {M : LB B.left} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂)
    {T : Over S'} (x y : T ⟶ B') {T₀ : Over S} {x₁ y₁ : T₀ ⟶ B} {t : LB.Gen (LB.LinComb M (lamPts x₁ y₁) negε)}
    (ht : t.IsGen) (r : T.left ⟶ T₀.left) (hx : x.left ≫ β = r ≫ x₁.left) (hy : y.left ≫ β = r ≫ y₁.left)
    {z : T.left} {J J₀ : (T.left ⟶ B.left) → M.ι} (hJ : Good M z J) (hJ₀ : Good M z J₀) :
    val t r z J = (tr M β₂ (lift x y).left z J J₀)⁻¹ * val t r z J₀ := by
  let ρ : Over.mk (r ≫ T₀.hom) ⟶ T₀ := Over.homMk r rfl
  refine (gen_trans ht r z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg (· * _) ?_)
  unfold tr
  rw [lift_sq hs x y (ρ ≫ x₁) (ρ ≫ y₁) hx.symm hy.symm]
  refine Eq.trans ?_ (congrArg (·⁻¹) (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x₁) (ρ ≫ y₁)
    (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q))))).symm
  rw [← MonObj.comp_mul, ← MonObj.comp_one ρ]
  have key : ∀ H : (T.left ⟶ B.left) → (T.left.presheaf.stalk z)ˣ, ∏ k, H (r ≫ lamPts x₁ y₁ k) ^ negε k =
      (H (ρ ≫ (x₁ * y₁)).left * (H (ρ ≫ x₁).left)⁻¹ * (H (ρ ≫ y₁).left)⁻¹ * H (ρ ≫ 1).left)⁻¹ := fun H => by
    rw [Fin.prod_univ_four]
    show H (ρ ≫ (x₁ * y₁)).left ^ (-1 : ℤ) * H (ρ ≫ x₁).left ^ (1 : ℤ) * H (ρ ≫ y₁).left ^ (1 : ℤ) *
      H (ρ ≫ 1).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one, mul_inv, inv_inv]
  exact key (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))

theorem one_push {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ B).left = (1 : T ⟶ B').left ≫ β := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((1 : T ⟶ B').left ≫ β) (by
    have := h.1.w
    have e := Over.w (1 : T ⟶ B')
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) this).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) e))))
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have : x₀ = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  rw [← this]; rfl

theorem psum_one {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (hx : ∀ k, ρ ≫ x k = 1) (I : Finset (Fin n)) :
    ρ ≫ psum B x I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one ρ
  | cons k l ih =>
    refine (MonObj.comp_mul ρ (x k) _).trans ?_
    exact (congrArg₂ (· * ·) (hx k) ih).trans (_root_.mul_one _)

theorem origin_pts {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β)
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) (T : Over S') (I : Finset (Fin 2)) :
    (lift (1 : T ⟶ B') (1 : T ⟶ B')).left ≫ β₂ ≫ (psum B (x2 B) I).left = (1 : T ⟶ B').left ≫ β := by
  rw [← Category.assoc, lift_sq hs 1 1 (1 : Over.mk (T.hom ≫ f) ⟶ B) 1 (one_push h T) (one_push h T), ← one_push h T]
  refine congrArg (·.left) (psum_one (lift (1 : Over.mk (T.hom ≫ f) ⟶ B) 1) (x2 B) (fun k => ?_) I)
  fin_cases k
  · exact lift_fst _ _
  · exact lift_snd _ _

theorem tr_origin {M : LB B.left} {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β)
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) (T : Over S') (z : T.left) (J J₀ : (T.left ⟶ B.left) → M.ι) :
    tr M β₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J₀ = 1 := by
  unfold tr
  rw [lift_sq hs 1 1 (1 : Over.mk (T.hom ≫ f) ⟶ B) 1 (one_push h T) (one_push h T)]
  refine (GlobalTheory.PrimCocycle.prod_lam (1 : Over.mk (T.hom ≫ f) ⟶ B) 1
    (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))).trans ?_
  rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end General

def scale {X : Scheme.{0}} {N : LB X} (t : N.Gen) (u : Γ(X, ⊤)ˣ) : N.Gen := ⟨fun i => t.s i * res le_top u⟩

theorem scale_isGen {X : Scheme.{0}} {N : LB X} {t : N.Gen} (ht : t.IsGen) (u : Γ(X, ⊤)ˣ) : (scale t u).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have := congrArg (gm (𝟙 X) x (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  show gm _ _ _ (_ * _) = _ * gm _ _ _ (_ * _)
  rw [map_mul, map_mul, gm_res _ x _ hx.1, gm_res _ x _ hx.2, this, _root_.mul_assoc]

theorem exists_norm {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁}
    {B' : Over (Sp R)} [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left}
    {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB) {f : Sp R ⟶ S} {f₁ : Sp R ⟶ S₁} {β : B'.left ⟶ B.left}
    {β₁ : B'.left ⟶ B₁.left} (h : IsGrpPullback B' B f β) (h₁ : IsGrpPullback B' B₁ f₁ β₁)
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left} (hs : IsSquare β β₂) (hs₁ : IsSquare β₁ β₂')
    (H : LBIso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) :
    ∃ w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'), w.IsGen ∧ IsNormIso w := by
  obtain ⟨w, hw⟩ := H
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  let ρ : TK R ⟶ T := Over.homMk (jK R) (Category.comp_id _)
  let e : Sp R ⟶ (G2 B').left := (lift (1 : T ⟶ B') (1 : T ⟶ B')).left
  have he : jK R ≫ e = (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left := by
    have : ρ ≫ lift (1 : T ⟶ B') (1 : T ⟶ B') = lift (1 : TK R ⟶ B') (1 : TK R ⟶ B') := by
      rw [comp_lift, MonObj.comp_one]
    exact congrArg (·.left) this
  let m : Sp R := closedPoint R
  obtain ⟨i, hi⟩ := exists_chart hM (((1 : T ⟶ B').left ≫ β) m)
  obtain ⟨i₁, hi₁⟩ := exists_chart hM₁ (((1 : T ⟶ B').left ≫ β₁) m)
  let P : (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).ι := (fun _ _ => i₁, fun _ _ => i)
  have hm : e m ∈ (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P :=
    ⟨mem_pull.2 (Set.mem_iInter.2 fun I => by
        have := congrArg (fun q => q m) (origin_pts h₁ hs₁ T I.down)
        exact (congrArg (· ∈ M₁.U i₁) this).mpr hi₁),
      mem_pull.2 (Set.mem_iInter.2 fun I => by
        have := congrArg (fun q => q m) (origin_pts h hs T I.down)
        exact (congrArg (· ∈ M.U i) this).mpr hi)⟩
  have htop : (⊤ : (Sp R).Opens) ≤ e ⁻¹ᵁ (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hm).ge
  let u : Γ(Sp R, ⊤)ˣ := res htop (pullU e _ (w.s P))
  refine ⟨scale w (pullU (G2 B').hom ⊤ u)⁻¹, scale_isGen hw _, fun z J J' hJ hJ' => ?_⟩
  have hz : (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z ∈
      (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P := by
    rw [← he]; exact htop (Set.mem_univ (jK R z))
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good M₁ hM₁ z (K := PUnit) (fun _ => (1 : TK R ⟶ B').left ≫ β₁) (fun _ => i₁)
    (fun _ _ _ => rfl) (fun _ => by
      have := congrArg (fun q => q z) (origin_pts h₁ hs₁ (TK R) ∅)
      exact (congrArg (· ∈ M₁.U i₁) this).mp (Set.mem_iInter.1 (mem_pull.1 hz.1) ⟨∅⟩))
  obtain ⟨J₀', hJ₀', e₀'⟩ := exists_good M hM z (K := PUnit) (fun _ => (1 : TK R ⟶ B').left ≫ β) (fun _ => i)
    (fun _ _ _ => rfl) (fun _ => by
      have := congrArg (fun q => q z) (origin_pts h hs (TK R) ∅)
      exact (congrArg (· ∈ M.U i) this).mp (Set.mem_iInter.1 (mem_pull.1 hz.2) ⟨∅⟩))
  rw [isoVal_trans (scale_isGen hw _) _ hJ hJ₀ hJ' hJ₀', tr_origin h hs, tr_origin h₁ hs₁, inv_one, _root_.mul_one,
    _root_.one_mul]
  have hP : ((fun _ I => J₀ ((lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
      fun _ I => J₀' ((lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left ≫ β₂ ≫ (psum B (x2 B) I.down).left)) :
        (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).ι) = P :=
    Prod.ext (funext fun _ => funext fun I => (congrArg J₀ (origin_pts h₁ hs₁ (TK R) I.down)).trans (e₀ PUnit.unit))
      (funext fun _ => funext fun I => (congrArg J₀' (origin_pts h hs (TK R) I.down)).trans (e₀' PUnit.unit))
  refine (congrArg (fun Q => gm (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z _
    ((scale w (pullU (G2 B').hom ⊤ u)⁻¹).s Q)) hP).trans ?_
  refine (map_mul _ _ _).trans (mul_eq_one_iff_eq_inv.2 ?_)
  refine Eq.symm ((congrArg (·⁻¹) ((gm_res _ z _ hz _).trans (map_inv _ _))).trans ((inv_inv _).trans ?_))
  refine (gm_pull _ (G2 B').hom z ⊤ trivial u).trans ?_
  refine (congrArg (fun q => gm q z ⊤ u) (Over.w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')))).trans ?_
  refine (gm_res (jK R) z htop trivial _).trans ((gm_pull (jK R) e z _ (htop (Set.mem_univ _)) _).trans ?_)
  exact congrArg (fun q => gm q z _ (w.s P)) he

theorem exists_const {K : Type} [Field K] (z : Sp K) (s : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = s := by
  obtain ⟨U, hU, a, ha⟩ := (Sp K).presheaf.germ_exist s.val
  have htop : (⊤ : (Sp K).Opens) ≤ U := fun y _ => by
    have : y = z := Subsingleton.elim (α := PrimeSpectrum K) y z
    exact this ▸ hU
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have e : φ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((Sp K).presheaf.map (homOfLE htop).op).hom a)) = s.val := by
    show ((Sp K).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _)) = _
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE htop) z trivial _).trans ha
  obtain ⟨k, hk⟩ : ∃ k : K, φ k = s.val := ⟨_, e⟩
  refine ⟨Units.mk0 k (fun h0 => s.ne_zero (by rw [← hk, h0, map_zero])), Units.ext ?_⟩
  exact (gm_val _ z ⊤ trivial _).trans hk

theorem exists_normIso_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen ∧ IsNormIso w₁ ∧ PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ _ _ _ _ h h₁ hs hs₁ H x hx
  obtain ⟨w, hw, hn⟩ := exists_norm D.toPre.P.isLB L.T.M.isLB h h₁ hs hs₁ H
  have key : ∀ a b, ∃ k : (FractionRing V₁)ˣ, ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ →
      ∀ z J J', Good L.T.M.L z J → Good D.toPre.P.L z J' →
      val (D.toPre.tau (e₀ (e a)) (e₀ (e b))) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn k) *
        (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
          val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J) := by
    intro a b
    by_cases hκ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁
    swap
    · exact ⟨1, fun κK h => (hκ ⟨κK, h⟩).elim⟩
    obtain ⟨κ, hκ⟩ := hκ
    let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
    choose J₀ hJ₀ using fun χ : (TK V₁).left ⟶ L.T.B.left => exists_chart L.T.M.isLB (χ z)
    choose J₀' hJ₀' using fun χ : (TK V₁).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    obtain ⟨t, ht, et⟩ := Wit.exists_tau D.toPre (e₀ (e a)) (e₀ (e b))
    obtain ⟨k, hk⟩ := exists_const (K := FractionRing V₁) z (val t κ z J₀' *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J₀ J₀' *
          val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J₀)⁻¹)
    refine ⟨k, fun κK hK z' J J' hJ hJ' => ?_⟩
    obtain rfl : κK = κ := by
      have : Mono (jK V) := Wit.mono_jK
      exact (cancel_mono (jK V)).1 (hK.trans hκ.symm)
    obtain rfl : z = z' := Subsingleton.elim (α := PrimeSpectrum (FractionRing V₁)) _ _
    have p₁ : ∀ a, (toUnit (TK V₁) ≫ x a).left ≫ β' = κK ≫ (toUnit (TK V) ≫ D.toPre.c (e₀ (e a))).left := fun a =>
      (Category.assoc (jK V₁) (x a).left β').trans ((congrArg (jK V₁ ≫ ·) (hx a).1).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hK.symm).trans (Category.assoc _ _ _))))
    have p₂ : ∀ a, (toUnit (TK V₁) ≫ x a).left ≫ β'' = ((TK V₁).hom ≫ spMap κ₁) ≫ (L.T.c₀ ((n : ℤ) • a)).left :=
      fun a => (Category.assoc (jK V₁) (x a).left β'').trans ((congrArg (jK V₁ ≫ ·) (hx a).2).trans
        (Category.assoc _ _ _).symm)
    have e₁ := val_trans hs _ _ ht κK (p₁ a) (p₁ b) hJ' hJ₀'
    have e₂ := val_trans hs₁ _ _ (L.T.τ₀_gen ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) (p₂ a) (p₂ b) hJ hJ₀
    have e₃ := isoVal_trans hw (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left hJ hJ₀ hJ' hJ₀'
    have alg : ∀ {U : Type} [CommGroup U] (A C p q s : U), A⁻¹ * p = p * (q * s)⁻¹ * (C * A⁻¹ * q * (C⁻¹ * s)) := by
      intro U _ A C p q s
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    have hk' : gm (𝟙 (TK V₁).left) z ⊤ (unitOn k) = _ := hk
    exact (et _ κK z J' hJ').symm.trans (e₁.trans ((alg _ _ _ _ _).trans
      (congrArg₂ (fun u v : ((TK V₁).left.presheaf.stalk z)ˣ => u * v) hk' (congrArg₂ (· * ·) e₃ e₂)).symm))
  choose q hq using key
  exact ⟨w, q, hw, hn, fun κK hK a b z J J' hJ hJ' => hq a b κK hK z J J' hJ hJ'⟩

end GlobalTheory.TChart.Ratio
