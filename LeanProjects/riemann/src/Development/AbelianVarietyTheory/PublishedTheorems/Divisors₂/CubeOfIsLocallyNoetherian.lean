import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeModel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

def pts {T : Over S} (a b c : T ⟶ A) : Fin 8 → (T.left ⟶ A.left) :=
  fun k ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left

theorem comp_pts {T Z : Over S} (w : Z ⟶ T) (a b c : T ⟶ A) (k : Fin 8) :
    w.left ≫ pts a b c k = pts (w ≫ a) (w ≫ b) (w ≫ c) k := by
  refine (Over.comp_left _ _ _ w _).symm.trans (congrArg (fun q : Z ⟶ A ↦ q.left) ?_)
  fin_cases k <;> simp [MonObj.comp_mul]

theorem prod_pts {T : Over S} (a b c : T ⟶ A) (h : a = 1 ∨ b = 1 ∨ c = 1) (U : Type) [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i, k (pts a b c i) ^ (![1, -1, -1, -1, 1, 1, 1, -1] : Fin 8 → ℤ) i = 1 := by
  rcases h with rfl | rfl | rfl <;>
  · simp only [Fin.prod_univ_eight, pts, _root_.one_mul, _root_.mul_one, Matrix.cons_val, zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

theorem cube_of_isLocallyNoetherian [IsLocallyNoetherian S] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB)
    (T : Over S) (a b c : T ⟶ A) :
    Triv (LB.LinComb L (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]) := by
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ A.left) → U),
        ∏ i, k (r ≫ pts (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, -1, 1, 1, 1, -1] : Fin 8 → ℤ) i = 1 := by
    intro Z r i b h U _ k
    obtain ⟨w, hw, h'⟩ := GlobalTheory.Biadditive.exists_over r i b h
    have := prod_pts (w ≫ x3 A 0) (w ≫ x3 A 1) (w ≫ x3 A 2) (by
      fin_cases i
      exacts [Or.inl h', Or.inr (Or.inl h'), Or.inr (Or.inr h')]) U k
    simp only [← comp_pts, hw] at this
    exact this
  obtain ⟨t, ht⟩ := CubeNoeth.triv_of_faces GlobalTheory.laws_without_cohomology.1 hA hL
    (pts (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, -1, 1, 1, 1, -1]
    (fun r i b h ↦ trivAt_of_formal hL r (formal r i b h)) (fun r b h ↦ formal r 0 b h)
  have c₀ : TrivAt L (pts (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, -1, 1, 1, 1, -1] (lift a (lift b c)).left :=
    ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k ↦ (lift a (lift b c)).left ≫ pts (x3 A 0) (x3 A 1) (x3 A 2) k) = pts a b c := funext fun k ↦ by
    rw [comp_pts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  exact c₀

theorem cube_ell {R : Type} [CommRing R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    IsAbelianScheme (WeierstrassCurve.ellPolAV W).A ∧ (WeierstrassCurve.ellPolAV W).L.IsLB ∧
    ∀ (T : Over (Spec (CommRingCat.of R))) (a b c : T ⟶ (WeierstrassCurve.ellPolAV W).A),
      Triv (LB.LinComb (WeierstrassCurve.ellPolAV W).L
        (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1]) :=
  ⟨(WeierstrassCurve.ellPolAV W).isAb, (WeierstrassCurve.ellPolAV W).isLB,
    cube_of_isLocallyNoetherian (WeierstrassCurve.ellPolAV W).isAb _ (WeierstrassCurve.ellPolAV W).isLB⟩

theorem pic_of_cube (h : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (x : GlobalTheory.CechPic.Pic A.left) (T : Over S)
    (a b c : T ⟶ A) :
    GlobalTheory.CechPic.pull (a * b * c).left x + GlobalTheory.CechPic.pull a.left x + GlobalTheory.CechPic.pull b.left x +
                 GlobalTheory.CechPic.pull c.left x =
      GlobalTheory.CechPic.pull (a * b).left x + GlobalTheory.CechPic.pull (a * c).left x + GlobalTheory.CechPic.pull (b * c).left x +
        GlobalTheory.CechPic.pull (1 : T ⟶ A).left x := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj x
  have z := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (h S A hA L hL T a b c)
  rw [GlobalTheory.CechPic.cls_linComb hL, Fin.sum_univ_eight] at z
  simp only [Matrix.cons_val, one_smul, neg_smul] at z
  rw [← sub_eq_zero, ← z]
  abel

end GlobalTheory.CubeModel
