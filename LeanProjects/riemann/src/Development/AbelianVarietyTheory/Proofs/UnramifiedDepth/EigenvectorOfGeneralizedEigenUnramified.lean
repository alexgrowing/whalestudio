import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GenEigen

theorem mem_of_add_nil {B : Type*} [CommRing B] (J : Ideal B) (u N y : B)
    (hu : ∀ b, u * b ∈ J → b ∈ J) (k : ℕ) (hN : N ^ k ∈ J) (h : (u + N) * y ∈ J) : y ∈ J := by
  have hpow : ∀ (j : ℕ) b, u ^ j * b ∈ J → b ∈ J := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      apply hu
      apply ih
      rwa [← mul_assoc, ← pow_succ]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow u (-N) k
  apply hpow k
  have e : u ^ k * y = c * ((u + N) * y) + ((-1) ^ k * y) * N ^ k := by
    have : u ^ k = (u - -N) * c + (-N) ^ k := by rw [← hc]; ring
    rw [this, neg_pow N]; ring
  rw [e]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ hN)

theorem step {O B : Type*} [CommRing O] [CommRing B] (a p : O →+* B) (J : Ideal B)
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d) (ε : O)
    (h1 : ∃ y, ε * ε - ε = (l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (l ^ d) - x) = (l : O) * y)
    (hS : ∀ y, (l : B) * (a y - p y) ∈ J)
    (hreg : ∀ (e : O) b, p (1 + l * e) * b ∈ J → b ∈ J)
    (hnil : ∀ x, ∃ k : ℕ, (a x - p x) ^ k ∈ J)
    (hlim : ∃ n : ℕ, 1 - a (ε ^ (l ^ n)) ∈ J) (x : O) : a x - p x ∈ J := by
  have hε : a ε - p ε ∈ J := by
    obtain ⟨y, hy⟩ := h1
    obtain ⟨k, hk⟩ := hnil ε
    have ha : a ε * a ε - a ε = l * a y := by simpa using congrArg a hy
    have hp : p ε * p ε - p ε = l * p y := by simpa using congrArg p hy
    refine mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_
    · intro b hb
      apply hreg (4 * y)
      have : p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b) := by
        simp only [map_add, map_mul, map_one, map_natCast, map_ofNat]
        linear_combination (-4 * b) * hp
      rw [this]
      exact J.mul_mem_left _ hb
    · have : (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y) := by
        linear_combination ha - hp
      rw [this]
      exact hS y
  have ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J := by
    obtain ⟨y, hy⟩ := h2 x
    obtain ⟨n, hn⟩ := hlim
    have ha : a ε * (a x ^ (l ^ d) - a x) = l * a y := by simpa using congrArg a hy
    have hp : p ε * (p x ^ (l ^ d) - p x) = l * p y := by simpa using congrArg p hy
    set s := a x ^ (l ^ d) - a x
    set t := p x ^ (l ^ d) - p x
    have h3 : a ε * (s - t) ∈ J := by
      have : a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε) := by
        linear_combination ha - hp
      rw [this]
      exact J.sub_mem (hS y) (J.mul_mem_left _ hε)
    obtain ⟨j, hj⟩ : ∃ j, l ^ n = j + 1 := ⟨l ^ n - 1, by have := pow_pos hl n; omega⟩
    rw [hj, map_pow] at hn
    have : s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t)) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)
  obtain ⟨H, hH⟩ := Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)
  obtain ⟨k, hk⟩ := hnil x
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1)
    (H * (a x - p x)) _ ?_ k ?_ ?_
  · intro b hb
    apply hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))
    have : p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b =
        -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b) := by
      simp only [map_add, map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]
      ring
    rw [this]
    exact J.neg_mem hb
  · rw [mul_pow]; exact J.mul_mem_left _ hk
  · have e : p x + (a x - p x) = a x := by ring
    rw [e] at hH
    have : (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x)
        = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x) := by
      rw [hH]; ring
    rw [this]
    exact ht

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_one_add_mul {e z : C} {m : ℝ} (he : V.Ge 1 e) (h : V.Ge m ((1 + e) * z)) :
    V.Ge m z := by
  have h0 : V.v (1 + e) = 0 := by
    have : V.v 1 < V.v e := by
      rw [V.v.map_one]
      exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) he
    rw [V.v.map_add_eq_of_lt_left this, V.v.map_one]
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, zero_add] at h

theorem exists_ge (z : C) : ∃ m : ℝ, V.Ge m z := by
  unfold VF.Ge
  induction V.v z using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem eq_zero_of_forall_ge {z : C} (m : ℝ) (h : ∀ k : ℕ, V.Ge (m + k) z) : z = 0 := by
  by_contra hz
  have hne : V.v z ≠ ⊤ := by
    intro ht
    have h1 : V.v (z * z⁻¹) = ⊤ := by rw [V.v.map_mul, ht, top_add]
    rw [mul_inv_cancel₀ hz, V.v.map_one] at h1
    exact WithTop.zero_ne_top h1
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk⟩ := exists_nat_gt (t - m)
  have := h k
  unfold VF.Ge at this
  rw [← ht] at this
  have : m + k ≤ t := by exact_mod_cast this
  linarith

theorem ge_mulVec {κ : Type} [Fintype κ] {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j))
    {z : κ → C} {m : ℝ} (hz : ∀ i, V.Ge m (z i)) (i : κ) : V.Ge m (M.mulVec z i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)

def levelIdeal {κ : Type} [Fintype κ] [DecidableEq κ] {B : Type} [CommRing B]
    (Φ : B →+* Matrix κ κ C) (hΦ : ∀ b i j, V.Ge 0 (Φ b i j)) (w : κ → C) (m : ℝ) : Ideal B where
  carrier := {b | ∀ i, V.Ge m ((Φ b).mulVec w i)}
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Matrix.add_mulVec]
    exact (ha i).add (hb i)
  zero_mem' := by
    intro i
    rw [map_zero, Matrix.zero_mulVec]
    exact VF.Ge.zero m
  smul_mem' := by
    intro c b hb i
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec]
    exact ge_mulVec (hΦ c) hb i

theorem eigen_of_gen_eigen (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type)
    [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C) (hL : ∀ x i j, V.Ge 0 (L x i j))
    (d : ℕ) (hd : 0 < d) (ε : O) (h1 : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) (ψ : O →+* C) (w : κ → C)
    (hψ : ∀ x, V.Ge 0 (ψ x))
    (hnil : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0)
    (hlim : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i))
    (x : O) : (L x).mulVec w = ψ x • w := by
  let P : O →+* Matrix κ κ C := (algebraMap C (Matrix κ κ C)).comp ψ
  have hP : ∀ x, P x = ψ x • (1 : Matrix κ κ C) := fun x => Algebra.algebraMap_eq_smul_one (ψ x)
  let Φ : O ⊗[ℤ] O →+* Matrix κ κ C :=
    (Algebra.TensorProduct.lift L.toIntAlgHom P.toIntAlgHom
      (fun x y => (Algebra.commutes (ψ y) (L x)).symm)).toRingHom
  have hΦt : ∀ x y, Φ (x ⊗ₜ y) = ψ y • L x := by
    intro x y
    change L x * P y = _
    rw [hP, Matrix.mul_smul, mul_one]
  have hΦ : ∀ b i j, V.Ge 0 (Φ b i j) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => intro i j; rw [map_zero]; exact VF.Ge.zero 0
    | tmul x y => intro i j; rw [hΦt]; exact (hψ y).mul_int (hL x i j)
    | add a b ha hb => intro i j; rw [map_add]; exact (ha i j).add (hb i j)
  let a : O →+* O ⊗[ℤ] O := Algebra.TensorProduct.includeLeftRingHom
  let p : O →+* O ⊗[ℤ] O := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] O ⊗[ℤ] O).toRingHom
  have ha : ∀ x, Φ (a x) = L x := fun x => by
    change Φ (x ⊗ₜ 1) = _
    rw [hΦt, map_one, one_smul]
  have hp : ∀ x, Φ (p x) = ψ x • (1 : Matrix κ κ C) := fun x => by
    change Φ (1 ⊗ₜ x) = _
    rw [hΦt, map_one]
  have mem : ∀ m b, b ∈ levelIdeal Φ hΦ w m ↔ ∀ i, V.Ge m ((Φ b).mulVec w i) :=
    fun _ _ => Iff.rfl
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, ∀ i, V.Ge m0 (w i) := by
    choose f hf using fun i => exists_ge (V := V) (w i)
    obtain ⟨m0, hm0⟩ := (Set.finite_range f).bddBelow
    exact ⟨m0, fun i => (hf i).mono (hm0 ⟨i, rfl⟩)⟩
  have key : ∀ (k : ℕ) y, a y - p y ∈ levelIdeal Φ hΦ w (m0 + k) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [mem]
      rw [Nat.cast_zero, add_zero]
      exact ge_mulVec (hΦ _) hm0
    | succ k ih =>
      refine step a p _ V.l d V.l_prime.pos hd ε h1 h2 ?_ ?_ ?_ ?_
      · intro y
        rw [mem]
        intro i
        have := ((mem _ _).1 (ih y) i).l_mul
        rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec]
        exact this.mono (by push_cast; linarith)
      · intro e b hb
        rw [mem] at hb ⊢
        intro i
        have := hb i
        rw [map_mul, hp, Matrix.smul_mul, one_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
          map_add, map_one, map_mul, map_natCast] at this
        exact ge_of_one_add_mul (by simpa using (hψ e).l_mul) this
      · intro y
        obtain ⟨j, hj⟩ := hnil y
        refine ⟨j, (mem _ _).2 fun i => ?_⟩
        rw [map_pow, map_sub, ha, hp, hj]
        exact VF.Ge.zero _
      · obtain ⟨N, hN⟩ := exists_nat_ge (m0 + (k + 1 : ℕ))
        choose f hf using hlim N
        obtain ⟨n, hn⟩ := (Set.finite_range f).bddAbove
        refine ⟨n, (mem _ _).2 fun i => ?_⟩
        rw [map_sub, map_one, ha, Matrix.sub_mulVec, Matrix.one_mulVec]
        exact (hf i n (hn ⟨i, rfl⟩)).mono hN
  funext i
  have := eq_zero_of_forall_ge (V := V) m0 fun k => (mem _ _).1 (key k x) i
  rw [map_sub, ha, hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.GenEigen
