import Mathlib

open MvPolynomial

namespace GlobalTheory.Capelli

variable {K σ : Type*} [CommRing K]

theorem pderiv_swap (u v : σ) (P : MvPolynomial σ K) :
    pderiv u (pderiv v P) = pderiv v (pderiv u P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, Pi.single_apply, hp]
    split_ifs <;> simp <;> ring

theorem pderiv_X_mul' [DecidableEq σ] (v w : σ) (Q : MvPolynomial σ K) :
    pderiv v (X w * Q) = X w * pderiv v Q + (if v = w then Q else 0) := by
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply]
  by_cases h : v = w
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def polar (K : Type*) [CommRing K] (u v : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X u : MvPolynomial σ K)) ∘ₗ (pderiv v).toLinearMap

@[simp] theorem polar_apply (u v : σ) (P : MvPolynomial σ K) :
    polar K u v P = X u * pderiv v P := rfl

theorem polar_lie [DecidableEq σ] (u v w s : σ) :
    polar K u v * polar K w s - polar K w s * polar K u v =
      (if v = w then polar K u s else 0) - (if s = u then polar K w v else 0) := by
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, polar_apply, pderiv_X_mul',
    pderiv_swap v s]
  split_ifs <;> simp <;> ring

section Ops

variable {I J I' J' : Type*}

noncomputable def colOp (K : Type*) [CommRing K] [Fintype I] (z : I × J → σ) (k l : J) :
    Module.End K (MvPolynomial σ K) :=
  ∑ a, polar K (z (a, k)) (z (a, l))

noncomputable def rowOp (K : Type*) [CommRing K] [Fintype J] (z : I × J → σ) (a b : I) :
    Module.End K (MvPolynomial σ K) :=
  ∑ k, polar K (z (a, k)) (z (b, k))

noncomputable def mixedOp (K : Type*) [CommRing K] [Fintype I] [Fintype I'] (z : I × J → σ)
    (y : I' × J → σ) (k l : J) : Module.End K (MvPolynomial σ K) :=
  colOp K z k l - colOp K y l k

theorem colOp_apply [Fintype I] (z : I × J → σ) (k l : J) (P : MvPolynomial σ K) :
    colOp K z k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P := by
  simp [colOp, LinearMap.sum_apply]

theorem rowOp_apply [Fintype J] (z : I × J → σ) (a b : I) (P : MvPolynomial σ K) :
    rowOp K z a b P = ∑ k, X (z (a, k)) * pderiv (z (b, k)) P := by
  simp [rowOp, LinearMap.sum_apply]

theorem mixedOp_apply [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J → σ) (k l : J)
    (P : MvPolynomial σ K) :
    mixedOp K z y k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P -
      ∑ b, X (y (b, l)) * pderiv (y (b, k)) P := by
  simp [mixedOp, colOp_apply]

theorem rowOp_eq_colOp [Fintype J] (z : I × J → σ) (a b : I) :
    rowOp K z a b = colOp K (fun w : J × I => z w.swap) a b := rfl

theorem colOp_lie [Fintype I] [DecidableEq J] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : J) :
    colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j =
      (if j = k then colOp K z i l else 0) - (if l = i then colOp K z k j else 0) := by
  classical
  have h : colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j =
      ∑ a, ∑ b, (polar K (z (a, i)) (z (a, j)) * polar K (z (b, k)) (z (b, l)) -
        polar K (z (b, k)) (z (b, l)) * polar K (z (a, i)) (z (a, j))) := by
    simp only [colOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    exact congrArg₂ (· - ·) rfl Finset.sum_comm
  rw [h]
  simp only [polar_lie, hz.eq_iff, Prod.mk.injEq, Finset.sum_sub_distrib]
  refine congrArg₂ (· - ·) ?_ ?_
  · by_cases hjk : j = k <;> simp [hjk, colOp]
  · by_cases hli : l = i <;> simp [hli, colOp]

theorem rowOp_lie [Fintype J] [DecidableEq I] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : I) :
    rowOp K z i j * rowOp K z k l - rowOp K z k l * rowOp K z i j =
      (if j = k then rowOp K z i l else 0) - (if l = i then rowOp K z k j else 0) :=
  colOp_lie (fun w : J × I => z w.swap) (hz.comp Prod.swap_injective) i j k l

theorem commute_polar {u v w s : σ} (h₁ : v ≠ w) (h₂ : s ≠ u) :
    Commute (polar K u v) (polar K w s) := by
  classical
  have := polar_lie (K := K) u v w s
  rw [if_neg h₁, if_neg h₂, sub_zero] at this
  exact sub_eq_zero.mp this

theorem commute_colOp_colOp [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (i j : J) (k l : J') :
    Commute (colOp K z i j) (colOp K y k l) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    commute_polar (hzy _ _) (hzy _ _).symm

theorem commute_rowOp_rowOp [Fintype J] [Fintype J'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (a b : I) (c d : I') :
    Commute (rowOp K z a b) (rowOp K y c d) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    commute_polar (hzy _ _) (hzy _ _).symm

theorem commute_rowOp_colOp [Fintype J] [Fintype I'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (a b : I) (k l : J') :
    Commute (rowOp K z a b) (colOp K y k l) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    commute_polar (hzy _ _) (hzy _ _).symm

theorem commute_rowOp_colOp_self [Fintype I] [Fintype J] (z : I × J → σ)
    (hz : Function.Injective z) (a b : I) (k l : J) :
    Commute (rowOp K z a b) (colOp K z k l) := by
  classical
  have h : rowOp K z a b * colOp K z k l - colOp K z k l * rowOp K z a b =
      ∑ m, ∑ c, (polar K (z (a, m)) (z (b, m)) * polar K (z (c, k)) (z (c, l)) -
        polar K (z (c, k)) (z (c, l)) * polar K (z (a, m)) (z (b, m))) := by
    simp only [colOp, rowOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    exact congrArg₂ (· - ·) rfl Finset.sum_comm
  refine sub_eq_zero.mp ?_
  rw [h]
  simp [polar_lie, hz.eq_iff, ite_and]

theorem mixedOp_lie [Fintype I] [Fintype I'] [DecidableEq J] (z : I × J → σ)
    (hz : Function.Injective z) (y : I' × J → σ) (hy : Function.Injective y)
    (hzy : ∀ u w, z u ≠ y w) (i j k l : J) :
    mixedOp K z y i j * mixedOp K z y k l - mixedOp K z y k l * mixedOp K z y i j =
      (if j = k then mixedOp K z y i l else 0) - (if l = i then mixedOp K z y k j else 0) := by
  have h₁ := colOp_lie (K := K) z hz i j k l
  have h₂ := colOp_lie (K := K) y hy l k j i
  have h₃ := (commute_colOp_colOp (K := K) z y hzy i j l k).eq
  have h₄ := (commute_colOp_colOp (K := K) z y hzy k l j i).eq
  have h : mixedOp K z y i j * mixedOp K z y k l - mixedOp K z y k l * mixedOp K z y i j =
      (colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j) -
      (colOp K y l k * colOp K y j i - colOp K y j i * colOp K y l k) := by
    simp only [mixedOp, sub_mul, mul_sub, h₃, h₄]
    abel
  rw [h, h₁, h₂]
  simp only [mixedOp, eq_comm (a := k) (b := j), eq_comm (a := i) (b := l)]
  split_ifs <;> abel

theorem commute_mixedOp_mixedOp {I₁ I₂ I₃ I₄ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    [Fintype I₄] (z : I₁ × J → σ) (y : I₂ × J → σ) (z' : I₃ × J' → σ) (y' : I₄ × J' → σ)
    (hzz : ∀ u w, z u ≠ z' w) (hzy : ∀ u w, z u ≠ y' w) (hyz : ∀ u w, y u ≠ z' w)
    (hyy : ∀ u w, y u ≠ y' w) (i j : J) (k l : J') :
    Commute (mixedOp K z y i j) (mixedOp K z' y' k l) :=
  Commute.sub_left
    (Commute.sub_right (commute_colOp_colOp z z' hzz _ _ _ _) (commute_colOp_colOp z y' hzy _ _ _ _))
    (Commute.sub_right (commute_colOp_colOp y z' hyz _ _ _ _) (commute_colOp_colOp y y' hyy _ _ _ _))

theorem commute_rowOp_left_mixedOp [Fintype I] [Fintype I'] [Fintype J] (z : I × J → σ)
    (hz : Function.Injective z) (y : I' × J → σ) (hzy : ∀ u w, z u ≠ y w) (a b : I) (k l : J) :
    Commute (rowOp K z a b) (mixedOp K z y k l) :=
  Commute.sub_right (commute_rowOp_colOp_self z hz _ _ _ _) (commute_rowOp_colOp z y hzy _ _ _ _)

theorem commute_rowOp_right_mixedOp [Fintype I] [Fintype I'] [Fintype J] (z : I × J → σ)
    (y : I' × J → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w) (a b : I') (k l : J) :
    Commute (rowOp K y a b) (mixedOp K z y k l) :=
  Commute.sub_right (commute_rowOp_colOp y z (fun u w => (hzy w u).symm) _ _ _ _)
    (commute_rowOp_colOp_self y hy _ _ _ _)

end Ops

theorem cross_term {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l))
        (∑ b, X (y (b, k)) * pderiv (y (b, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  classical
  simp only [map_sum, pderiv_X_mul', if_neg (hzy _ _), add_zero, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ k, ∑ a, ∑ b, ∑ l, X (z (a, k)) * (X (y (b, k)) *
            pderiv (z (a, l)) (pderiv (y (b, l)) P)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        simp only [mul_assoc]

theorem cross_term' {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ b, X (y (b, k)) * pderiv (y (b, l))
        (∑ a, X (z (a, k)) * pderiv (z (a, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  rw [cross_term y z (fun u w => (hzy w u).symm), Finset.sum_comm]
  simp only [mul_comm (X (y _) : MvPolynomial σ K), pderiv_swap (y _) (z _)]

end GlobalTheory.Capelli

namespace GlobalTheory

open Capelli

theorem capelli_casimir {K σ : Type*} [CommRing K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l)) (∑ b, X (z (b, l)) * pderiv (z (b, k)) P)) =
    (∑ a, ∑ b, ∑ k, X (z (a, k)) * pderiv (z (b, k)) (∑ l, X (z (b, l)) * pderiv (z (a, l)) P)) +
      ((n : K) - (p : K)) • ∑ w : Fin p × Fin n, X (z w) * pderiv (z w) P := by
  set E : MvPolynomial σ K := ∑ w : Fin p × Fin n, X (z w) * pderiv (z w) P with hE
  set S : MvPolynomial σ K := ∑ a, ∑ b, ∑ k, ∑ l, X (z (a, k)) * (X (z (b, l)) *
    pderiv (z (a, l)) (pderiv (z (b, k)) P)) with hS
  have h₁ : (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l))
      (∑ b, X (z (b, l)) * pderiv (z (b, k)) P)) = S + (n : K) • E := by
    simp only [map_sum, pderiv_X_mul', hz.eq_iff, Prod.mk.injEq, and_true,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · calc _ = ∑ k, ∑ a, ∑ b, ∑ l, X (z (a, k)) * (X (z (b, l)) *
            pderiv (z (a, l)) (pderiv (z (b, k)) P)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    · rw [hE, Fintype.sum_prod_type_right, Finset.smul_sum]
      simp [Nat.cast_smul_eq_nsmul]
  have h₂ : (∑ a, ∑ b, ∑ k, X (z (a, k)) * pderiv (z (b, k))
      (∑ l, X (z (b, l)) * pderiv (z (a, l)) P)) = S + (p : K) • E := by
    simp only [map_sum, pderiv_X_mul', hz.eq_iff, Prod.mk.injEq, true_and,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [hS]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [pderiv_swap]
    · rw [hE, Fintype.sum_prod_type, Finset.smul_sum]
      simp [Nat.cast_smul_eq_nsmul]
  rw [h₁, h₂, sub_smul]
  abel

namespace Capelli

variable {K σ : Type*} [CommRing K] {p q n : ℕ}

theorem casimir_colOp (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, colOp K z k l (colOp K z l k P) =
      ∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P := by
  classical
  simp only [colOp_apply, rowOp_apply]
  rw [capelli_casimir z hz P, Fintype.sum_prod_type]

theorem casimir_mixedOp (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (y : Fin q × Fin n → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, mixedOp K z y k l (mixedOp K z y l k P) =
      (∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P) +
      (∑ a, ∑ b, rowOp K y a b (rowOp K y b a P) +
        ((n : K) - (q : K)) • ∑ a, rowOp K y a a P) -
      (2 : K) • ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  have c₁ := cross_term z y hzy P
  have c₂ := cross_term' z y hzy P
  simp only [← colOp_apply] at c₁ c₂
  rw [Finset.sum_comm] at c₂
  rw [← casimir_colOp z hz, ← casimir_colOp y hy, two_smul,
    Finset.sum_comm (f := fun k l => colOp K y k l (colOp K y l k P))]
  simp only [mixedOp, LinearMap.sub_apply, map_sub, Finset.sum_sub_distrib]
  rw [c₁, c₂]
  abel

end Capelli

end GlobalTheory
