import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

namespace GlobalTheory.RatioIneq

theorem chain_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ n : ℕ, ∀ i k : Fin a, (i : ℕ) + n = k →
      r i ≤ (max 1 t⁻¹ * ρ) ^ n * r k ∧ r k ≤ (max 1 t⁻¹ * ρ) ^ n * r i := by
  have hM1 : (1:ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hBρ : ρ ≤ max 1 t⁻¹ * ρ := le_mul_of_one_le_left (by linarith) hM1
  have hBt : t⁻¹ ≤ max 1 t⁻¹ * ρ :=
    (le_max_right 1 t⁻¹).trans (le_mul_of_one_le_right (by linarith) hρ)
  intro n
  induction n with
  | zero =>
    intro i k h
    have : i = k := Fin.ext (by simpa using h)
    subst this; simp
  | succ n ih =>
    intro i k h
    have hk' : (i : ℕ) + n < a := by have := k.isLt; omega
    obtain ⟨h1, h2⟩ := ih i ⟨i + n, hk'⟩ rfl
    have hkk : (k : ℕ) = ((⟨i + n, hk'⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have n1 : r ⟨i + n, hk'⟩ ≤ (max 1 t⁻¹ * ρ) * r k :=
      (hhi _ k hkk).trans (mul_le_mul_of_nonneg_right hBρ (hr k).le)
    have n2 : r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := by
      have hl := hlo _ k hkk
      have : r k ≤ t⁻¹ * r ⟨i + n, hk'⟩ := by
        calc r k = t⁻¹ * (t * r k) := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
          _ ≤ t⁻¹ * r ⟨i + n, hk'⟩ := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 ht.le)
      exact this.trans (mul_le_mul_of_nonneg_right hBt (hr _).le)
    have hB0 : 0 ≤ (max 1 t⁻¹ * ρ) := by linarith
    have hBn : 0 ≤ (max 1 t⁻¹ * ρ) ^ n := pow_nonneg hB0 n
    constructor
    · calc r i ≤ (max 1 t⁻¹ * ρ) ^ n * r ⟨i + n, hk'⟩ := h1
        _ ≤ (max 1 t⁻¹ * ρ) ^ n * ((max 1 t⁻¹ * ρ) * r k) := mul_le_mul_of_nonneg_left n1 hBn
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r k := by ring
    · calc r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := n2
        _ ≤ (max 1 t⁻¹ * ρ) * ((max 1 t⁻¹ * ρ) ^ n * r i) := mul_le_mul_of_nonneg_left h2 hB0
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r i := by ring

theorem pair_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) (i k : Fin a) :
    r i ≤ (max 1 t⁻¹ * ρ) ^ a * r k := by
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hi := i.isLt
  have hk := k.isLt
  rcases le_total (i : ℕ) k with h | h
  · obtain ⟨h1, -⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (k - i) i k (by omega)
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)
  · obtain ⟨-, h2⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (i - k) k i (by omega)
    exact h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)

theorem le_max_one_of_pow_le {x c : ℝ} {a : ℕ} (ha : a ≠ 0) (h : x ^ a ≤ c) : x ≤ max 1 c := by
  rcases le_total x 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · exact (le_self_pow₀ h1 ha).trans (h.trans (le_max_right _ _))

end GlobalTheory.RatioIneq

namespace GlobalTheory.RatioIneq

theorem sum_add_inv_le_of_ratio_bounds :
    ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ,
      (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  intro a t c₁ c₂ ht hc₁
  refine ⟨a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a, a, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max 1 c₂ := (zero_le_one.trans (le_max_left _ _))
    have h2 : (0:ℝ) ≤ max 1 c₁⁻¹ := (zero_le_one.trans (le_max_left _ _))
    have h3 : (0:ℝ) ≤ max 1 t⁻¹ := (zero_le_one.trans (le_max_left _ _))
    positivity
  intro r hr hlo hP1 hP2 ρ hρ hhi
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hBa : 0 < (max 1 t⁻¹ * ρ) ^ a := pow_pos (by linarith) a
  have pb := pair_bound a t ρ ht hρ r hr hlo hhi
  have hup : ∀ i, r i ≤ max 1 c₂ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hx : ∀ k, r i / (max 1 t⁻¹ * ρ) ^ a ≤ r k := fun k => by
      rw [div_le_iff₀ hBa, mul_comm]; exact pb i k
    have hprod : (r i / (max 1 t⁻¹ * ρ) ^ a) ^ a ≤ ∏ k, r k := by
      have := Finset.prod_le_prod (s := Finset.univ)
        (f := fun _ : Fin a => r i / (max 1 t⁻¹ * ρ) ^ a) (g := r)
        (fun _ _ => (div_pos (hr i) hBa).le) (fun k _ => hx k)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have := le_max_one_of_pow_le ha (hprod.trans hP2)
    rwa [div_le_iff₀ hBa] at this
  have hdown : ∀ i, (r i)⁻¹ ≤ max 1 c₁⁻¹ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hy : 0 < (max 1 t⁻¹ * ρ) ^ a * r i := mul_pos hBa (hr i)
    have hprod : ∏ k, r k ≤ ((max 1 t⁻¹ * ρ) ^ a * r i) ^ a := by
      have := Finset.prod_le_prod (s := Finset.univ) (f := r)
        (g := fun _ : Fin a => (max 1 t⁻¹ * ρ) ^ a * r i)
        (fun k _ => (hr k).le) (fun k _ => pb k i)
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
    have hc : ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ ^ a ≤ c₁⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ hc₁ (hP1.trans hprod)
    have := le_max_one_of_pow_le ha hc
    have heq : (r i)⁻¹ = (max 1 t⁻¹ * ρ) ^ a * ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hBa.ne', one_mul]
    rw [heq, mul_comm (max 1 c₁⁻¹)]
    exact mul_le_mul_of_nonneg_left this hBa.le
  calc ∑ i, (r i + (r i)⁻¹)
      ≤ ∑ _i : Fin a, (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹ * ρ) ^ a :=
        Finset.sum_le_sum fun i _ => by rw [add_mul]; exact add_le_add (hup i) (hdown i)
    _ = a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a * ρ ^ a := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_pow]; ring

end GlobalTheory.RatioIneq
