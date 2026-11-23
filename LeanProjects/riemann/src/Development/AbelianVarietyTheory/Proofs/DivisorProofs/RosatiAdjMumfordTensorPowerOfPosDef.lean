import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Over S}
variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

def lamLeft (z : X ⟶ G) : (X ⟶ G) →* Multiplicative (Pic X.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_prod_left {κ : Type} [Fintype κ] (x : κ → (X ⟶ G)) (n : κ → ℤ) (z : X ⟶ G) :
    lam (cls L hL) (∏ i, x i ^ n i) z = ∑ i, n i • lam (cls L hL) (x i) z := by
  have h := congrArg Multiplicative.toAdd (map_prod (lamLeft hL hΘ z) (fun i => x i ^ n i) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  exact h

theorem lam_prod_right {κ : Type} [Fintype κ] (x : X ⟶ G) (z : κ → (X ⟶ G)) (n : κ → ℤ) :
    lam (cls L hL) x (∏ i, z i ^ n i) = ∑ i, n i • lam (cls L hL) x (z i) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ (z _) x]

theorem lam_mul_right (x y z : X ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

end Bilinear

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def pairP (T : Tens D D' W) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j)

theorem cls_tens (T : Tens D D' W) :
    cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (T.pr i) (T.pr j) := by
  have hC := LB.isLB_linComb D.P.isLB (tensφ T.pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨T.w, T.w_gen⟩).trans ?_
  rw [cls_linComb D.P.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_tens (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairP T W h h := by
  rw [cls_tens T, pairP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

end Tensor

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Tensor2

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pairP_mul (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairP T W (u * v) (u * v) = pairP T W u u + pairP T W v v + pairP T (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ T.pr i = u ≫ T.pr i * v ≫ T.pr i := fun i => by
    haveI := T.pr_hom i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (v ≫ T.pr i) (u ≫ T.pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairP, hm, lam_mul_left D.P.isLB hΘ, lam_mul_right D.P.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

def pre {X Y Z : Over (Spec (CommRingCat.of R))} [GrpObj Z] (u : X ⟶ Y) : (Y ⟶ Z) →* (X ⟶ Z) where
  toFun f := u ≫ f
  map_one' := by simp [Hom.one_def]
  map_mul' f g := MonObj.comp_mul u f g

theorem comp_act_pr (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ T.act m) ≫ T.pr i = ∏ k, (u ≫ T.pr k) ^ m i k := by
  rw [Category.assoc, Tens.act_pr]
  exact (map_prod (pre (Z := D.P.A) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := D.P.A) u) _ _)

theorem pairP_act_left (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M (u ≫ T.act m) v = pairP T (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_left D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairP_act_right (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M u (v ≫ T.act m) = pairP T (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_right D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end Tensor2

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem symUnit_mul_star (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    (W + W.transpose) * TensO.mat _ (star a) = (TensO.mat _ a).transpose * (W + W.transpose) := by
  have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show (W + W.transpose) * ((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)) = _
  rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem rosatiAdj_core (T : Tens D D' W) (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    RosatiAdj D'.P.A D'.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := T.act (TensO.mat _ a)
  let g := T.act (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_tens T]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairP_mul, pairP_mul]
    rw [pairP_act_left T (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairP_act_right T (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.RosatiTens

open GlobalTheory.Mum.RosatiTens in

theorem GlobalTheory.Mum.rosatiAdj_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact rosatiAdj_core T h a
