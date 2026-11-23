import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Finset

namespace GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

variable {R : Type} [CommRing R] {M : ℕ}

theorem trace_reindex_self {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag]
  exact e.symm.sum_comp (fun x => A x x)

theorem reindex_pow_self {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) (k : ℕ) :
    (Matrix.reindex e e A) ^ k = Matrix.reindex e e (A ^ k) := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def embF (x : Fin M × Fin M) (a b : Fin M) : R :=
  (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b -
    (1 : Matrix (Fin M) (Fin M) R) x.1 b * (1 : Matrix (Fin M) (Fin M) R) x.2 a

def emb (R : Type) [CommRing R] (M : ℕ) : Matrix (Fin M × Fin M) (Pair M) R :=
  Matrix.of fun x r => embF x r.1.1 r.1.2

theorem sum_mul_embF (A : Fin M × Fin M → R) (a b : Fin M) :
    ∑ y, A y * embF y a b = A (a, b) - A (b, a) := by
  simp [embF, Fintype.sum_prod_type, Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem sum_emb_mul (x : Fin M × Fin M) (G : Fin M → Fin M → R) (hG : ∀ a b, G b a = - G a b)
    (hG0 : ∀ a, G a a = 0) :
    ∑ q : Pair M, emb R M x q * G q.1.1 q.1.2 = G x.1 x.2 := by
  have h := sum_sum_eq_sum_pair (fun a b =>
    (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b)
  have hl : ∑ a, ∑ b, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b
      = G x.1 x.2 := by
    simp [Matrix.one_apply]
  have hd : ∑ a, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 a * G a a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hG0, mul_zero]
  rw [hl, hd, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [emb, embF, Matrix.of_apply, hG q.1.1 q.1.2]
  ring

theorem mul_emb_apply {n : Type} (A : Matrix n (Fin M × Fin M) R) (x : n) (r : Pair M) :
    (A * emb R M) x r = A x (r.1.1, r.1.2) - A x (r.1.2, r.1.1) := by
  rw [Matrix.mul_apply]
  exact sum_mul_embF (fun y => A x y) r.1.1 r.1.2

def wedgeLieExt (L : Matrix (Fin M) (Fin M) R) (a b : Fin M) (r : Pair M) : R :=
  L a r.1.1 * (1 : Matrix (Fin M) (Fin M) R) b r.1.2 + (1 : Matrix (Fin M) (Fin M) R) a r.1.1 * L b r.1.2 -
    L b r.1.1 * (1 : Matrix (Fin M) (Fin M) R) a r.1.2 - (1 : Matrix (Fin M) (Fin M) R) b r.1.1 * L a r.1.2

def tensorLie (L : Matrix (Fin M) (Fin M) R) : Matrix (Fin M × Fin M) (Fin M × Fin M) R :=
  Matrix.kroneckerMap (· * ·) L 1 + Matrix.kroneckerMap (· * ·) 1 L

theorem tensorLie_mul_emb (L : Matrix (Fin M) (Fin M) R) :
    tensorLie L * emb R M = emb R M * wedgeLieRaw L := by
  ext x r
  rw [mul_emb_apply, Matrix.mul_apply]
  have h := sum_emb_mul x (fun a b => wedgeLieExt L a b r)
    (fun a b => by simp only [wedgeLieExt]; ring) (fun a => by simp only [wedgeLieExt]; ring)
  rw [show (∑ q : Pair M, emb R M x q * wedgeLieRaw L q r) =
      ∑ q : Pair M, emb R M x q * wedgeLieExt L q.1.1 q.1.2 r from rfl, h]
  simp only [tensorLie, wedgeLieExt, Matrix.add_apply, Matrix.kroneckerMap_apply]
  ring

theorem tensorLie_pow_mul_emb (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    tensorLie L ^ n * emb R M = emb R M * wedgeLieRaw L ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, tensorLie_mul_emb, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem emb_transpose_mul_emb :
    (emb R M)ᵀ * emb R M = (2 : R) • (1 : Matrix (Pair M) (Pair M) R) := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  rw [mul_emb_apply]
  simp only [Matrix.transpose_apply, emb, embF, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    Subtype.mk.injEq, Prod.mk.injEq, smul_eq_mul]
  simp only at hij hkl
  have h0 : ¬ (k = j ∧ l = i) := fun h => by
    rcases h with ⟨rfl, rfl⟩; exact absurd (hij.trans hkl) (lt_irrefl _)
  by_cases h1 : k = i <;> by_cases h2 : l = j
  · subst h1; subst h2; simp [hkl.ne, hkl.ne']; ring
  · have : ¬ (i = k ∧ j = l) := fun h => h2 h.2.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all

theorem emb_mul_transpose_apply (x y : Fin M × Fin M) :
    (emb R M * (emb R M)ᵀ) x y = embF x y.1 y.2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp only [mul_comm (emb R M x _)]
  exact sum_emb_mul y (fun a b => embF x a b) (fun a b => by simp only [embF]; ring)
    (fun a => by simp only [embF]; ring)

theorem trace_mul_emb_mul_transpose (A : Matrix (Fin M × Fin M) (Fin M × Fin M) R) :
    (A * (emb R M * (emb R M)ᵀ)).trace = A.trace - ∑ x : Fin M × Fin M, A x (x.2, x.1) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply]
  simp only [emb_mul_transpose_apply]
  exact sum_mul_embF (fun y => A x y) x.1 x.2

theorem sum_kron_swap (P Q : Matrix (Fin M) (Fin M) R) :
    ∑ x : Fin M × Fin M, Matrix.kroneckerMap (· * ·) P Q x (x.2, x.1) = (P * Q).trace := by
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply]

theorem kron_left_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R)) ^ m =
      Matrix.kroneckerMap (· * ·) (L ^ m) (1 : Matrix (Fin M) (Fin M) R) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem kron_right_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) ^ m =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) (L ^ m) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem sum_tensorLie_pow_swap (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    ∑ x : Fin M × Fin M, (tensorLie L ^ n) x (x.2, x.1) = 2 ^ n * (L ^ n).trace := by
  have hc : Commute (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R))
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) := by
    show _ * _ = _ * _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hterm : ∀ m ∈ Finset.range (n + 1), ∀ x : Fin M × Fin M,
      (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R) ^ m *
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L ^ (n - m) *
        ((n.choose m : ℕ) : Matrix (Fin M × Fin M) (Fin M × Fin M) R)) x (x.2, x.1) =
      (n.choose m : R) * Matrix.kroneckerMap (· * ·) (L ^ m) (L ^ (n - m)) x (x.2, x.1) := by
    intro m _ x
    rw [kron_left_pow, kron_right_pow, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
  have htr : ∀ m ∈ Finset.range (n + 1), (L ^ m * L ^ (n - m)).trace = (L ^ n).trace := by
    intro m hm
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
  rw [tensorLie, hc.add_pow]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun m hm => (Finset.sum_congr rfl fun x _ => hterm m hm x)]
  simp only [← Finset.mul_sum, sum_kron_swap]
  rw [Finset.sum_congr rfl fun m hm => by rw [htr m hm], ← Finset.sum_mul]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

end GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

namespace GlobalTheory.GoodMetric.ChernSpan

open TraceWedgeSq

theorem two_mul_trace_wedge2Lie_pow {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ) :
    2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  have hW : ((wedge2Lie L) ^ i).trace = ((wedgeLieRaw L) ^ i).trace := by
    rw [wedge2Lie, reindex_pow_self, trace_reindex_self]
  have hK : kron L 1 + kron 1 L = Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorLie L) := by
    ext a b
    simp [kron, tensorLie]
  rw [hW, hK, reindex_pow_self, trace_reindex_self]
  have key : (2 : R) • (wedgeLieRaw L ^ i) = (emb R M)ᵀ * (tensorLie L ^ i * emb R M) := by
    rw [tensorLie_pow_mul_emb, ← Matrix.mul_assoc, emb_transpose_mul_emb, Matrix.smul_mul, Matrix.one_mul]
  calc 2 * (wedgeLieRaw L ^ i).trace = ((2 : R) • (wedgeLieRaw L ^ i)).trace := by
        rw [Matrix.trace_smul, smul_eq_mul]
    _ = (tensorLie L ^ i * emb R M * (emb R M)ᵀ).trace := by rw [key, Matrix.trace_mul_comm]
    _ = _ := by rw [Matrix.mul_assoc, trace_mul_emb_mul_transpose, sum_tensorLie_pow_swap]

end GlobalTheory.GoodMetric.ChernSpan
