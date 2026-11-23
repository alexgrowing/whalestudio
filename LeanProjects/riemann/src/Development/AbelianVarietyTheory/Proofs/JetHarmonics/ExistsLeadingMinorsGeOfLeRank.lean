import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

namespace GlobalTheory

theorem exists_mem_valuation_le_of_mem_span {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by
  by_contra hne
  push Not at hne
  have key : ∀ y ∈ Submodule.span O A,
      v (algebraMap O C (φ y)) < v (algebraMap O C (φ x)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha => exact hne a ha
    | zero => simpa using pos_iff_ne_zero.mpr h0
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      exact v.map_add_lt ha hb
    | smul o a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one o)) ha
  exact lt_irrefl _ (key x hx)

theorem exists_leading_minors_ge_of_le_rank {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by
  have hvc : v (algebraMap O C c) ≠ 0 := by
    rw [Ne, v.zero_iff]
    intro h
    exact hc (hv.hom_inj (by rw [h, map_zero]))
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m hm h0
    obtain rfl : m = 0 := Nat.le_zero.mp h0
    simp
  | succ n ih =>
    intro hn
    obtain ⟨t, htA, ht⟩ := ih (Nat.le_of_succ_le hn)
    let coef : Fin (n + 1) → O := fun a => (-1) ^ ((a : ℕ) + n) *
      (Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b))).det
    let φ : (Fin r → O) →ₗ[O] O :=
      ∑ a : Fin (n + 1), coef a • LinearMap.proj (Fin.castLE hn a)
    have hφ : ∀ x, φ x = ∑ a : Fin (n + 1), coef a * x (Fin.castLE hn a) := by
      intro x
      simp [φ, LinearMap.sum_apply]
    have hdet : ∀ x, (Matrix.of fun a i : Fin (n + 1) =>
        Function.update t n x i (Fin.castLE hn a)).det = φ x := by
      intro x
      rw [hφ, Matrix.det_succ_column _ (Fin.last n)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : (Matrix.of fun a i : Fin (n + 1) =>
          Function.update t n x i (Fin.castLE hn a)).submatrix a.succAbove
          (Fin.last n).succAbove =
          Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b)) := by
        ext b i
        simp [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      rw [this]
      simp only [coef, Matrix.of_apply, Fin.val_last, Function.update_self]
      ring
    have hval : φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1) =
        c * (Matrix.of fun a i : Fin n => t i (Fin.castLE (Nat.le_of_succ_le hn) a)).det := by
      rw [map_smul, smul_eq_mul, hφ, Finset.sum_eq_single (Fin.last n)]
      · congr 1
        simp only [coef, Pi.single_eq_same, mul_one, Fin.val_last, Fin.succAbove_last]
        rw [← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, one_mul]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne (fun h => hb (Fin.castLE_injective hn h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlow : v (algebraMap O C c) ^ (n + 1) ≤
        v (algebraMap O C (φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1))) := by
      rw [hval, map_mul, map_mul, pow_succ']
      exact mul_le_mul_right (ht n _ le_rfl) _
    obtain ⟨a, haA, ha⟩ := exists_mem_valuation_le_of_mem_span v hv A φ (hA _)
      (ne_of_gt (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.mpr hvc) _) hlow))
    refine ⟨Function.update t n a, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt h)]
        exact htA i h
      · rw [Function.update_self]
        exact haA
    · intro m hm hmn
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · have h' : m ≤ n := Nat.lt_succ_iff.mp h
        have : (Matrix.of fun b i : Fin m => Function.update t n a i (Fin.castLE hm b)) =
            Matrix.of fun b i : Fin m => t i (Fin.castLE hm b) := by
          ext b i
          simp [Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le i.isLt h'))]
        rw [this]
        exact ht m hm h'
      · rw [hdet]
        exact hlow.trans ha

theorem exists_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by
  intro C _ v O _ _ hv r A c hc hA
  obtain ⟨t, htA, ht⟩ := exists_leading_minors_ge_of_le_rank v hv A hc hA r le_rfl
  exact ⟨fun i => t i, fun i => htA i i.isLt, fun s => ht (s.val + 1) s.isLt s.isLt⟩

end GlobalTheory
