import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.SuperTrace

variable {n : ℕ}

def Sg (m : ℕ) (z : Big n) : Prop :=
  ∀ a : Fin n, ((1 : Ext n) ⊗ₜ vec n a) * z = (-1) ^ m * (z * ((1 : Ext n) ⊗ₜ vec n a))

theorem sg_zero (m : ℕ) : Sg m (0 : Big n) := by intro a; simp

theorem sg_add {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by
  intro a; rw [mul_add, hz a, hw a, add_mul, mul_add]

theorem sg_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using sg_zero m
  | cons x s hx ih =>
    rw [Finset.sum_cons]
    exact sg_add (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sg_mul {m l : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg l w) : Sg (m + l) (z * w) := by
  intro a
  have hc : Commute ((-1 : Big n) ^ l) z := (Commute.neg_one_left z).pow_left l
  rw [← mul_assoc, hz a, mul_assoc, mul_assoc, hw a, pow_add, ← mul_assoc z, ← hc.eq]
  simp only [mul_assoc]

theorem sg_one : Sg 0 (1 : Big n) := by intro a; simp

theorem sg_left (x : Ext n) : Sg 0 (x ⊗ₜ (1 : Ext n)) := by
  intro a; simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem sg_right (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by
  intro a
  simp [Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n a b, TensorProduct.tmul_neg]

def MSg {r s : Type*} (m : ℕ) (M : Matrix r s (Big n)) : Prop := ∀ i j, Sg m (M i j)

theorem msg_mul {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by
  intro i j; rw [Matrix.mul_apply]; exact sg_sum _ _ _ fun k _ => sg_mul (hM i k) (hN k j)

theorem msg_one {r : Type*} [Fintype r] [DecidableEq r] : MSg 0 (1 : Matrix r r (Big n)) := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact sg_one
  · exact sg_zero 0

theorem msg_pow {r : Type*} [Fintype r] [DecidableEq r] {M : Matrix r r (Big n)} (hM : MSg 1 M)
    (j : ℕ) : MSg j (M ^ j) := by
  induction j with
  | zero => simpa using (msg_one : MSg 0 (1 : Matrix r r (Big n)))
  | succ j ih => rw [pow_succ]; exact msg_mul ih hM

theorem pow_mul_left {p q : ℕ} {R : Type*} [Semiring R] (A : Matrix (Fin p) (Fin q) R)
    (B : Matrix (Fin q) (Fin p) R) (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc A B A]

theorem trace_swap {p q : ℕ} (A : Matrix (Fin p) (Fin q) (Big n)) (B : Matrix (Fin q) (Fin p) (Big n))
    (hA : MSg 0 A) (hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a) (m : ℕ) :
    ((B * A) ^ (m + 1)).trace = (-1) ^ m * ((A * B) ^ (m + 1)).trace := by
  have hB1 : MSg 1 B := by
    intro b i; obtain ⟨a, ha⟩ := hB b i; rw [ha]; exact sg_right a
  have hY : MSg m (A * (B * A) ^ m) := by
    simpa using msg_mul hA (msg_pow (by simpa using msg_mul hB1 hA) m)
  have h1 : (B * A) ^ (m + 1) = B * (A * (B * A) ^ m) := by
    rw [pow_succ', Matrix.mul_assoc]
  have h2 : (A * B) ^ (m + 1) = (A * (B * A) ^ m) * B := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_left]
  generalize A * (B * A) ^ m = Y at hY h1 h2
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a, ha⟩ := hB b i
  rw [ha, hY i b a]

theorem val_trace {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by
  simp [Matrix.trace, map_sum]

theorem val_pow {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k :=
  map_pow ((EvenPart n).val.toRingHom.mapMatrix) M k

end GlobalTheory.GrassModel.SuperTrace

open GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace in
theorem GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar {n p q : ℕ}
    (e : Fin p × Fin q → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    ((blockPoly e).map (toEven n) ^ k).trace + ((-blockPolyBar e).map (toEven n) ^ k).trace = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set A : Matrix (Fin p) (Fin q) (Big n) := Matrix.of fun i b => vec n (e (i, b)) ⊗ₜ (1 : Ext n)
  set B : Matrix (Fin q) (Fin p) (Big n) := Matrix.of fun b j => (1 : Ext n) ⊗ₜ vec n (e (j, b))
  have hA : MSg 0 A := fun i b => sg_left _
  have hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a := fun b i => ⟨e (i, b), rfl⟩
  have hL : ((blockPoly e).map (toEven n)).map (EvenPart n).val = A * B := by
    ext i j
    simp [A, B, blockPoly, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hD : (Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = B * A := by
    ext i j
    simp [A, B, blockPolyBar, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hneg : (-blockPolyBar e).map (toEven n) = -((blockPolyBar e).map (toEven n)) := by
    ext i j; simp
  apply Subtype.val_injective
  show (EvenPart n).val (_ + _) = (EvenPart n).val 0
  rw [map_add, map_zero, hneg, ← Matrix.trace_transpose (( -_ ) ^ _), Matrix.transpose_pow,
    Matrix.transpose_neg, val_trace, val_trace, val_pow, val_pow, hL]
  rw [show (-Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = -(B * A) by
    rw [← hD]; ext i j; simp]
  rcases Nat.even_or_odd (m + 1) with h | h
  · rw [h.neg_pow, trace_swap A B hA hB m]
    have : Odd m := by rcases h with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    rw [this.neg_one_pow]; simp
  · rw [h.neg_pow, Matrix.trace_neg, trace_swap A B hA hB m]
    have : Even m := by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩
    rw [this.neg_one_pow]; simp
