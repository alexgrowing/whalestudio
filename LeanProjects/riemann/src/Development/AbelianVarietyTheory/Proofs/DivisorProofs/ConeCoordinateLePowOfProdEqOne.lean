import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem coneChain_step_bounds {a : ℕ} {t ρ K : ℝ} (ht : 0 < t) (hKt : t⁻¹ ≤ K) (hK0 : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hup : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hdown : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ k : ℕ, ∀ i j : Fin a, (j : ℕ) = i + k → r j ≤ K ^ k * r i ∧ r i ≤ ρ ^ k * r j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by simpa using hij)
    subst hji
    simp
  | succ k ih =>
    intro i j hij
    have hja := j.isLt
    have hk : (i : ℕ) + k < a := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hk⟩ rfl
    have hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have hu := hup _ j hmj
    have hd := hdown _ j hmj
    set m : Fin a := ⟨(i : ℕ) + k, hk⟩
    have hrj : r j ≤ t⁻¹ * r m := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    constructor
    · calc r j ≤ t⁻¹ * r m := hrj
        _ ≤ K * r m := mul_le_mul_of_nonneg_right hKt (hr m).le
        _ ≤ K * (K ^ k * r i) := mul_le_mul_of_nonneg_left h1.1 hK0
        _ = K ^ (k + 1) * r i := by ring
    · calc r i ≤ ρ ^ k * r m := h1.2
        _ ≤ ρ ^ k * (ρ * r j) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) * r j := by ring

theorem coneCoord_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  intro a t ht
  obtain ⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K := ⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K ^ a, one_le_pow₀ hK1, ?_⟩
  intro r ρ hr hup hprod hρ hdown i
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hC0 : 0 ≤ K ^ a * ρ ^ a := mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  have step := coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown
  have pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q := by
    intro p q
    rcases le_total (q : ℕ) p with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := p.isLt; omega
      calc r p ≤ K ^ k * r q := (step k q p hk).1
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc K ^ k ≤ K ^ a := pow_le_pow_right₀ hK1 hka
            _ = K ^ a * 1 := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ) (pow_nonneg hK0 _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := q.isLt; omega
      calc r p ≤ ρ ^ k * r q := (step k p q hk).2
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc ρ ^ k ≤ ρ ^ a := pow_le_pow_right₀ hρ hka
            _ = 1 * ρ ^ a := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (pow_nonneg hρ0 _)
  have hne : (Finset.univ : Finset (Fin a)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have ex_le : ∃ j, r j ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r)
      (fun _ _ => one_pos) (fun j _ => hcon j) hne
    simp [hprod] at this
  have ex_ge : ∃ j, 1 ≤ r j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ))
      (fun j _ => hr j) (fun j _ => hcon j) hne
    simp [hprod] at this
  obtain ⟨j, hj⟩ := ex_le
  obtain ⟨l, hl⟩ := ex_ge
  constructor
  · calc r i ≤ K ^ a * ρ ^ a * r j := pair i j
      _ ≤ K ^ a * ρ ^ a * 1 := mul_le_mul_of_nonneg_left hj hC0
      _ = K ^ a * ρ ^ a := by ring
  · rw [inv_eq_one_div, div_le_iff₀ (hr i)]
    have := pair l i
    linarith

end GlobalTheory
