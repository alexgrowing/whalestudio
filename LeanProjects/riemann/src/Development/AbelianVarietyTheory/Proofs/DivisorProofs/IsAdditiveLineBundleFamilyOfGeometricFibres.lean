import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.ZM GlobalTheory.AbLaw.CubeGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddFib

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def quad {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) : Fin 4 → (Z.left ⟶ (A ⊗ T).left) :=
  ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left, (lift 1 y).left]

abbrev uquad (A T : Over S) [GrpObj A] : Fin 4 → ((A ⊗ (A ⊗ T)).left ⟶ (A ⊗ T).left) :=
  quad (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

theorem comp_quad {Z Z' : Over S} (r : Z' ⟶ Z) (x x' : Z ⟶ A) (y : Z ⟶ T) (i : Fin 4) :
    r.left ≫ quad x x' y i = quad (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem prod_quad {Z : Over S} {x x' : Z ⟶ A} (y : Z ⟶ T) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (Z.left ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (quad x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, quad, -Over.comp_left]
  · simp [Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]

theorem homMk_comp_eq_one {Y : Over S} {Z : Scheme.{0}} (r : Z ⟶ Y.left) (u : Y ⟶ A) (b : Z ⟶ S)
    (h : r ≫ u.left = b ≫ η[A].left) : (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) ≫ u = 1 := by
  have hb : b = r ≫ Y.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem formal_quad {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ T)).left) (b : Z ⟶ S)
    (h : r ≫ (fst A (A ⊗ T)).left = b ≫ η[A].left ∨ r ≫ (snd A (A ⊗ T) ≫ fst A T).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (r ≫ uquad A T i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  have e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T))
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T)
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i :=
    fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i
  simp only [e]
  exact prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k

theorem triv_quad_iff {N : LB (A ⊗ T).left} (hN : N.IsLB) {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) :
    Triv (LB.LinComb N (quad x x' y) ![1, -1, -1, 1]) ↔
      evc hN (x * x') y - evc hN x y - evc hN x' y + evc hN 1 y = 0 := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_
  rw [cls_linComb hN, Fin.sum_univ_four]
  have e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d :=
    fun a b c d ↦ by simp only [one_smul, neg_smul]; abel
  simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
  rw [e]
  rfl

omit [GrpObj A] in

theorem exists_chart {X : Scheme.{0}} (j : X ⟶ T.left) :
    ∃ q : ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).left ⟶ (A ⊗ (A ⊗ T)).left,
      IsPullback q ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).hom
        (snd A (A ⊗ T) ≫ snd A T).left j ∧
      q ≫ (fst A (A ⊗ T)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T) ≫ fst A T).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) := by
  set B := (Over.pullback (j ≫ T.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧
      m ≫ (snd A T).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A T).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom := by
    rw [← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom
      (m ≫ (A ⊗ T).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left,
      q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

theorem isAdditive_of_geomFibres (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (N : LB (A ⊗ T).left) (hN : N.IsLB) (h0 : Triv (ev N (1 : T ⟶ A) (𝟙 T)))
    (hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T),
      IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) : IsAdditive N := by
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  have := hA.geomConnected
  have := hA.smooth
  have := hA.proper
  have one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0 := fun y ↦ by
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  have H := GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left
    (fun R _ _ j ↦ by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_chart (A := A) j
    have hB := isAb_baseChange hA (j ≫ T.hom)
    have one := one_left_fst (A := A) (j ≫ T.hom)
    let B := (Over.pullback (j ≫ T.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB := DVR.linComb_isLB _ hN _ _
    have pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M) := fun M hM ↦
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN' (pf _ hN') ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left := fun t ↦ by
    let K := AlgebraicClosure (T.left.residueField t)
    let g : Spec (CommRingCat.of K) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t
    let s : Sp K ⟶ S := g ≫ T.hom
    let t' : Over.mk s ⟶ T := Over.homMk g rfl
    have hadd := hgeo K s t'
    let π := pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g
    let f' := pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g
    refine ⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩
    · have := (Scheme.range_fromSpecResidueField t).le
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩
      exact this
    let Zs : Over S := Over.mk (f' ≫ s)
    have w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s := by
      rw [← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]
    let x : Zs ⟶ A ⊗ (A ⊗ T) := Over.homMk π w
    let τ : Zs ⟶ Over.mk s := Over.homMk f' rfl
    have hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t' := Over.OverMorphism.ext pullback.condition
    have hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB := pull_isLB hN _
    have ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T) := fun a ↦ by
      rw [evc_ev hN, lift_fst, lift_snd_assoc, hx]
    have e := (isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ
    rw [ev₁, ev₁, ev₁] at e
    have ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T)
        (x ≫ snd A (A ⊗ T) ≫ snd A T) := funext fun k ↦ comp_quad x _ _ _ k
    unfold TrivAt
    rw [ef, triv_quad_iff hN, one₁, e]
    abel
  let e : T ⟶ A ⊗ (A ⊗ T) := lift 1 (lift 1 (𝟙 T))
  have e₀ : e ≫ fst A (A ⊗ T) = 1 := by simp [e]
  have e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _ := by simp [e]
  have htr := triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left
    (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_))
    (fun V ↦ ?_) (fun s ↦ H.1 (all s))
  rotate_left
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_chart (A := A) V.ι
    have hB := isAb_baseChange hA (V.ι ≫ T.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  have h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left := by
    have h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _) := by
      unfold TrivAt; simp only [Category.id_comp]; exact htr
    have := h0'.comp (lift a (lift a' t)).left
    rwa [Category.comp_id] at this
  have ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t := funext fun k ↦ by
    rw [comp_quad]; simp only [lift_fst, lift_snd_assoc, lift_snd]
  have h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1]) := by
    have h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1]) := h1
    rwa [ef] at h1'
  have h3 := (triv_quad_iff hN a a' t).1 h2
  rw [one₁, add_zero, sub_sub, sub_eq_zero] at h3
  exact h3

end GlobalTheory.AddFib
