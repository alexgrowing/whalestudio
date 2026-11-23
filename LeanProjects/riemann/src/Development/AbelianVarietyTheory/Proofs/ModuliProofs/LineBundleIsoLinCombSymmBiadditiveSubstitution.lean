import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.BilinCalc

theorem sum_antisymm {M : Type*} [AddCommGroup M] {n : ℕ} (b : Fin n → Fin n → M) (hb : ∀ i j, b i j = b j i)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : ∀ i j, D i j + D j i = 0) :
    ∑ uv : Fin n × Fin n, D uv.1 uv.2 • b uv.1 uv.2 = 0 := by
  classical

  let E : Fin n → Fin n → ℤ := fun i j => if i < j then D i j else 0
  have hDE : ∀ i j, D i j = E i j - E j i := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [E, hij, not_lt.mpr hij.le]
    · have := hD i i
      simp [E]
      omega
    · have := hD i j
      simp [E, hij, not_lt.mpr hij.le]
      omega
  have hswap : ∑ uv : Fin n × Fin n, E uv.2 uv.1 • b uv.1 uv.2 =
      ∑ uv : Fin n × Fin n, E uv.1 uv.2 • b uv.1 uv.2 := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun uv => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hb]
  simp only [hDE, sub_smul, Finset.sum_sub_distrib, hswap, sub_self]

theorem map_prod_zpow {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℤ) : f (∏ i, x i ^ c i) = ∑ i, c i • f (x i) := by
  let φ : Additive G →+ M := AddMonoidHom.mk' (fun a => f a.toMul) fun a a' => hf _ _
  have hφ : ∀ g : G, f g = φ (Additive.ofMul g) := fun _ => rfl
  rw [hφ, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, ← hφ]

theorem sum_subst {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n m : ℕ} (x : Fin n → G)
    (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (h : W' + W'.transpose = c.transpose * (W + W.transpose) * c) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • B (x uv.1) (x uv.2) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) := by
  classical
  have hL : ∀ (y : G) (k : Fin n → ℤ), B (∏ i, x i ^ k i) y = ∑ i, k i • B (x i) y :=
    fun y k => map_prod_zpow (fun g => B g y) (fun g g' => hB g g' y) x k
  have hR : ∀ (z : G) (k : Fin n → ℤ), B z (∏ i, x i ^ k i) = ∑ i, k i • B z (x i) :=
    fun z k => map_prod_zpow (fun g => B z g) (fun g g' => by rw [hs z, hB, hs g, hs g']) x k

  have hV : ∀ i j, ∑ a : Fin m, ∑ a' : Fin m, W a a' * (c a i * c a' j) = (c.transpose * W * c) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) =
      ∑ ij : Fin n × Fin n, (c.transpose * W * c) ij.1 ij.2 • B (x ij.1) (x ij.2) := by
    simp only [hL, hR, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, ← hV, Finset.sum_smul]
    calc _ = ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n, ∑ a' : Fin m,
          (W a a' * (c a i * c a' j)) • B (x i) (x j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  refine sum_antisymm (fun i j => B (x i) (x j)) (fun i j => hs _ _) (W' - c.transpose * W * c) fun i j => ?_
  have hij := congrFun (congrFun h i) j
  have ht : (c.transpose * W * c).transpose = c.transpose * W.transpose * c := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hji := congrFun (congrFun ht i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_add, Matrix.add_mul] at hij hji
  simp only [Matrix.sub_apply]
  linarith

open GlobalTheory.CechPic in

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  intro S A _ _ Pb hPb hbi hsym T n m x W W' c h
  classical

  let β : (T ⟶ A) → (T ⟶ A) → Pic T.left := fun u v => pull (lift u v).left (cls Pb hPb)
  have hadd : ∀ u u' v : T ⟶ A, β (u * u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨t, ht⟩ := (hbi T u u' v).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hPb _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hPb] at e
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at e
    simp only [β]
    rw [← sub_eq_zero, ← e]
    abel
  have hsw : ∀ u v : T ⟶ A, β u v = β v u := by
    intro u v
    have e : cls Pb hPb = cls _ (pull_isLB hPb _) := (cls_eq_iff hPb (pull_isLB hPb _)).2 hsym
    rw [cls_pull hPb] at e
    simp only [β]
    conv_lhs => rw [e, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  refine (cls_eq_iff (LB.isLB_linComb hPb _ _) (LB.isLB_linComb hPb _ _)).1 ?_
  rw [cls_linComb hPb, cls_linComb hPb]
  exact sum_subst β hadd hsw x W W' c h

end GlobalTheory.BilinCalc
