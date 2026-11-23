import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem eis_U_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) (n : ℕ) (hn : n ≠ 0) :
    eis j c a b (l * n) = t * eis j c a b n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  have hln : l * n ≠ 0 := mul_ne_zero hl0 hn
  simp only [eis, hln, hn, if_false]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1, l * p.2)) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
    refine ⟨?_, hln⟩
    rw [← hp.1]; ring
  · intro p _ _ q _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hl.pos h.2)
  · intro q hq hne
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have h1 : ¬ l ∣ q.1 := by
      intro hd
      apply hne
      rw [ha q.1 (by exact_mod_cast hd)]; ring
    have h2 : l ∣ q.2 := by
      have : l ∣ q.1 * q.2 := by rw [hq.1]; exact dvd_mul_right _ _
      exact (hl.dvd_mul.mp this).resolve_left h1
    obtain ⟨y, hy⟩ := h2
    refine ⟨(q.1, y), ?_, ?_, ?_⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, hn⟩
      have h := hq.1
      rw [hy] at h
      have : l * (q.1 * y) = l * n := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hl.pos this
    · intro h0
      apply hne
      have : b (q.2 : ℤ) = t * b (y : ℤ) := by rw [hy]; push_cast; exact hb _
      rw [this]
      simp only at h0
      linear_combination h0
    · ext <;> simp [hy]
  · intro p _ _
    simp only
    push_cast
    rw [hb]; ring

theorem eis_V_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x, a (l * x) = t * a x) (n : ℕ) (hn : n ≠ 0) :
    eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  by_cases hd : l ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl.pos]
    simp only [eis, hn, hm, if_false]
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp _
      rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
      refine ⟨?_, hn⟩
      rw [← hp.1]; ring
    · intro p _ _ q _ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl.pos h.1) h.2
    · intro q hq hne
      rw [Nat.mem_divisorsAntidiagonal] at hq
      have h1 : l ∣ q.1 := by
        by_contra h
        apply hne
        have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by exact_mod_cast h
        simp [this]
      obtain ⟨x, hx⟩ := h1
      refine ⟨(x, q.2), ?_, ?_, ?_⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        refine ⟨?_, hm⟩
        have h := hq.1
        rw [hx] at h
        have : l * (x * q.2) = l * m := by rw [← h]; ring
        exact Nat.eq_of_mul_eq_mul_left hl.pos this
      · intro h0
        apply hne
        have hdv : (l : ℤ) ∣ (q.1 : ℤ) := by rw [hx]; push_cast; exact dvd_mul_right _ _
        simp only [hdv, if_true]
        have : a (q.1 : ℤ) = t * a (x : ℤ) := by rw [hx]; push_cast; exact ha _
        rw [this, hx]
        simp only at h0
        push_cast
        rw [mul_pow]
        linear_combination h0
      · ext <;> simp [hx]
    · intro p _ _
      have hdv : (l : ℤ) ∣ ((l * p.1 : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
      simp only [hdv, if_true]
      push_cast
      rw [ha, mul_pow]; ring
  · have h0 : Vo l (eis j c a b) n = 0 := by simp [Vo, hd]
    rw [h0, mul_zero]
    simp only [eis, hn, if_false]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by
      intro h
      apply hd
      have h' : l ∣ q.1 := by exact_mod_cast h
      rw [← hq.1]; exact dvd_mul_of_dvd_left h' _
    simp [this]

theorem eis_U_V (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) : l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) :=
  fun hl => ⟨fun ha hb n hn => eis_U_pair j l c t a b hl ha hb n hn,
    fun _ ha n hn => eis_V_pair j l c t a b hl ha n hn⟩

end GlobalTheory
