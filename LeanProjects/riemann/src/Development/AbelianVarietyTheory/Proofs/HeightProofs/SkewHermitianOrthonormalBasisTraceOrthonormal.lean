import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.KOrth

theorem trE {n : ℕ} (a b c d : Fin n) : trace (unitE a b * unitE c d) = if b = c ∧ a = d then 1 else 0 := by
  simp only [unitE]
  by_cases h : b = c
  · subst h; rw [Matrix.single_mul_single_same]
    by_cases h2 : a = d
    · subst h2; simp
    · simp [h2, Matrix.trace_single_eq_of_ne _ _ _ h2]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]; simp [h]

theorem s2 : invSqrtTwo * invSqrtTwo = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem mem_pairs_lt {n : ℕ} {ε : Fin n → Bool} {s : Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε s) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs {n : ℕ} (ε : Fin n → Bool) (s : Bool) : (pairs ε s).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

section
variable {n : ℕ}

theorem d_self (a : Fin n) : trace ((Complex.I • unitE a a) * (Complex.I • unitE a a)) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp

theorem d_ne {a b : Fin n} (h : a ≠ b) : trace ((Complex.I • unitE a a) * (Complex.I • unitE b b)) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp [h]

theorem trace_casimirAntisymPair_mul_self {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * (invSqrtTwo • (unitE a b - unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (-2 : ℂ) * s2

theorem trace_casimirSymPairI_mul_self {a b : Fin n} (h : a < b) :
    trace (((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (2 * invSqrtTwo * invSqrtTwo) * Complex.I_mul_I - (2 : ℂ) * s2

theorem p12 {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.trace_add, Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  ring

theorem dp1 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * (invSqrtTwo • (unitE b c - unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem dp2 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * ((invSqrtTwo * Complex.I) • (unitE b c + unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem pq_facts {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ¬ (p.2 = q.1 ∧ p.1 = q.2) ∧ ¬ (p.2 = q.2 ∧ p.1 = q.1) ∧ ¬ (p.1 = q.1 ∧ p.2 = q.2) ∧
      ¬ (p.1 = q.2 ∧ p.2 = q.1) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => hpq (Prod.ext h2 h1), fun ⟨h1, h2⟩ => hpq (Prod.ext h1 h2),
    fun ⟨h1, h2⟩ => ?_⟩
  · have := hp.trans_eq h1; have := hq.trans_eq h2.symm; exact absurd (hp.trans (h1 ▸ h2 ▸ hq)) (lt_irrefl _)
  · exact absurd (hp.trans (h2 ▸ h1 ▸ hq)) (lt_irrefl _)

end
end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis.KOrth
variable {n : ℕ}

theorem pq_zero {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ∀ X ∈ [invSqrtTwo • (unitE p.1 p.2 - unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 + unitE p.2 p.1)],
    ∀ Y ∈ [invSqrtTwo • (unitE q.1 q.2 - unitE q.2 q.1), (invSqrtTwo * Complex.I) • (unitE q.1 q.2 + unitE q.2 q.1)],
    trace (X * Y) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := pq_facts hp hq hpq
  have e1 : trace (unitE p.1 p.2 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h1]
  have e2 : trace (unitE p.1 p.2 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h2]
  have e3 : trace (unitE p.2 p.1 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h3]
  have e4 : trace (unitE p.2 p.1 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h4]
  intro X hX Y hY
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub, e1, e2, e3, e4] <;> simp

theorem kList_self (ε : Fin n → Bool) : ∀ X ∈ kList ε, trace (X * X) = -1 := by
  intro X hX
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, rfl | rfl⟩
  · exact d_self a
  · exact trace_casimirAntisymPair_mul_self (mem_pairs_lt hp)
  · exact trace_casimirSymPairI_mul_self (mem_pairs_lt hp)

theorem kList_pairwise (ε : Fin n → Bool) : (kList ε).Pairwise (fun X Y => trace (X * Y) = 0) := by
  rw [kList, List.pairwise_append, List.pairwise_map, List.pairwise_flatMap]
  refine ⟨(List.nodup_finRange n).imp fun h => d_ne h, ⟨fun p hp => ?_, ?_⟩, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, List.forall_mem_nil]
    exact ⟨p12 (mem_pairs_lt hp), fun _ h => h.elim⟩
  · exact (nodup_pairs ε true).imp_of_mem fun hp hq hpq => pq_zero (mem_pairs_lt hp) (mem_pairs_lt hq) hpq
  · intro X hX Y hY
    simp only [List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX hY
    obtain ⟨a, -, rfl⟩ := hX
    obtain ⟨p, hp, rfl | rfl⟩ := hY
    · exact dp1 a (mem_pairs_lt hp)
    · exact dp2 a (mem_pairs_lt hp)

end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis

theorem kB_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length),
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  intro n ε i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, kB, KOrth.kList_self ε _ (List.get_mem _ _)]; simp
  · rw [if_neg hij]
    have hP := List.pairwise_iff_get.mp (KOrth.kList_pairwise ε)
    rcases lt_or_gt_of_ne hij with h | h
    · rw [kB, hP i j h]; simp
    · rw [kB, Matrix.trace_mul_comm, hP j i h]; simp

end GlobalTheory.TypeSum.CasBasis

end
