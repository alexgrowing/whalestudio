import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem prod_max_inv_le_prod_max {ι : Type} [Fintype ι] (x : ι → ℝ) (hx : ∀ v, 0 < x v) (h1 : 1 ≤ ∏ v, x v) :
    ∏ v, max 1 (x v)⁻¹ ≤ ∏ v, max 1 (x v) := by
  have key : ∀ v, max 1 (x v) = x v * max 1 (x v)⁻¹ := by
    intro v
    rcases le_total 1 (x v) with h | h
    · rw [max_eq_right h, max_eq_left (inv_le_one_of_one_le₀ h), mul_one]
    · rw [max_eq_left h, max_eq_right ((one_le_inv₀ (hx v)).2 h), mul_inv_cancel₀ (hx v).ne']
  have h0 : 0 ≤ ∏ v, max 1 (x v)⁻¹ :=
    Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _)
  calc ∏ v, max 1 (x v)⁻¹ = 1 * ∏ v, max 1 (x v)⁻¹ := (one_mul _).symm
    _ ≤ (∏ v, x v) * ∏ v, max 1 (x v)⁻¹ := mul_le_mul_of_nonneg_right h1 h0
    _ = ∏ v, max 1 (x v) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (key v).symm

theorem fold_max_le_prod_max {n : ℕ} (x : Fin n → ℝ) :
    Finset.univ.fold max 1 x ≤ ∏ l, max 1 (x l) := by
  have hge : ∀ l, (1 : ℝ) ≤ max 1 (x l) := fun l => le_max_left _ _
  have hone : ∀ s : Finset (Fin n), (1 : ℝ) ≤ ∏ l ∈ s, max 1 (x l) := by
    intro s
    calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ l ∈ s, max 1 (x l) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun l _ => hge l)
  refine (Finset.fold_max_le _).2 ⟨hone _, fun l _ => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  calc x l ≤ max 1 (x l) * 1 := by rw [mul_one]; exact le_max_right _ _
    _ ≤ max 1 (x l) * ∏ m ∈ Finset.univ.erase l, max 1 (x m) :=
      mul_le_mul_of_nonneg_left (hone _) (le_trans zero_le_one (hge l))

theorem prod_fold_inv_le {ι : Type} [Fintype ι] {n : ℕ} (P : ℝ) (hP : 1 ≤ P) (Dm : ι → Fin n → ℝ) (De sg : ι → ℝ)
    (hD : ∀ l, (∀ v, Dm v l = 0) ∨ ((∀ v, 0 < Dm v l) ∧ 1 ≤ ∏ v, Dm v l))
    (hDe : ∀ v, De v = Finset.univ.fold max 1 fun l => (Dm v l)⁻¹)
    (hsg : ∀ v, sg v = Finset.univ.fold max 1 fun l => Dm v l / P) :
    ∏ v, De v ≤ ∏ v, (P * sg v) ^ n := by
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  have hsg1 : ∀ v, 1 ≤ sg v := fun v => by
    rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have hPsg : ∀ v, 1 ≤ P * sg v := fun v => one_le_mul_of_one_le_of_one_le hP (hsg1 v)
  have hcol : ∀ l, ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, P * sg v := by
    intro l
    rcases hD l with h0 | ⟨hpos, hprod⟩
    · calc ∏ v, max 1 (Dm v l)⁻¹ = ∏ _v : ι, (1 : ℝ) :=
            Finset.prod_congr rfl fun v _ => by simp [h0 v]
        _ ≤ ∏ v, P * sg v := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => hPsg v)
    · calc ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, max 1 (Dm v l) :=
            prod_max_inv_le_prod_max (fun v => Dm v l) hpos hprod
        _ ≤ ∏ v, P * sg v := by
          refine Finset.prod_le_prod (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun v _ => ?_)
          have h1 : Dm v l / P ≤ sg v := by
            rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inr ⟨l, Finset.mem_univ _, le_rfl⟩)
          refine max_le (hPsg v) ?_
          calc Dm v l = P * (Dm v l / P) := by field_simp
            _ ≤ P * sg v := mul_le_mul_of_nonneg_left h1 hP0.le
  calc ∏ v, De v ≤ ∏ v, ∏ l, max 1 (Dm v l)⁻¹ := by
        refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
        · rw [hDe v]; exact le_trans zero_le_one ((Finset.le_fold_max _).2 (Or.inl le_rfl))
        · rw [hDe v]; exact fold_max_le_prod_max (fun l => (Dm v l)⁻¹)
    _ = ∏ l, ∏ v, max 1 (Dm v l)⁻¹ := Finset.prod_comm
    _ ≤ ∏ _l : Fin n, ∏ v, P * sg v :=
        Finset.prod_le_prod (fun l _ => Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _))
          (fun l _ => hcol l)
    _ = ∏ v, (P * sg v) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]

theorem const_loss_le (r : ℕ) (hr : 1 ≤ r) (H : ℝ) (hH : 1 ≤ H) :
    16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
      ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) ≤ (8 * r * H) ^ (80 * r ^ 4) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hB8 : (8 : ℝ) ≤ 8 * r * H := by nlinarith
  have hB1 : (1 : ℝ) ≤ 8 * r * H := by linarith
  have hH0 : (0 : ℝ) ≤ 2 * H := by linarith
  have e1 : (16 : ℝ) ≤ (8 * r * H) ^ 2 := by nlinarith
  have e2 : (4 * r + 4 : ℝ) ≤ (8 * r * H) ^ 1 := by rw [pow_one]; nlinarith
  have e3 : (4 * r : ℝ) ≤ 8 * r * H := by nlinarith
  have e4 : 2 * H ≤ 8 * r * H := by nlinarith
  have hexp : 2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2)) ≤ 80 * r ^ 4 := by
    have p1 : r ^ 1 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p3 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p0 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
    rw [pow_one] at p1
    nlinarith
  calc 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
        ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2))
      ≤ (8 * r * H) ^ 2 * (8 * r * H) ^ 1 * (8 * r * H) ^ (4 * r ^ 2) * (8 * r * H) ^ (16 * r ^ 3 + 4 * r) *
        ((8 * r * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) := by
        have a1 := mul_le_mul e1 e2 (by positivity) (by positivity)
        have a2 := mul_le_mul a1 (pow_le_pow_left₀ (by positivity) e3 (4 * r ^ 2)) (by positivity) (by positivity)
        have a3 := mul_le_mul a2 (pow_le_pow_left₀ hH0 e4 (16 * r ^ 3 + 4 * r)) (pow_nonneg hH0 _) (by positivity)
        exact mul_le_mul a3 (pow_le_pow_left₀ (pow_nonneg hH0 _) (pow_le_pow_left₀ hH0 e4 _) _)
          (pow_nonneg (pow_nonneg hH0 _) _) (by positivity)
    _ = (8 * r * H) ^ (2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2))) := by
        rw [← pow_mul]; simp only [← pow_add]
    _ ≤ (8 * r * H) ^ (80 * r ^ 4) := pow_le_pow_right₀ hB1 hexp

theorem size_loss_le (C' : ℝ) (C₁ k r : ℕ) (hC : C' + 2 ≤ C₁) (hr : 1 ≤ r) (hk : 40 * r ^ 4 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    s ^ ((r + 1) * (8 * r ^ 2 + 2)) * s ^ (-((((C₁ * k * r : ℕ) : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) ≤ s ^ (-(C' * k)) := by
  have hs0 : 0 < s := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hk' : 40 * (r : ℝ) ^ 4 ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← Real.rpow_natCast, ← Real.rpow_add hs0]
  apply Real.rpow_le_rpow_of_exponent_le hs
  push_cast
  have hsplit : ((C₁ : ℝ) * k * r - 16 * r ^ 3 - 4 * r - 1) / r = C₁ * k - 16 * r ^ 2 - 4 - 1 / r := by
    field_simp
  have hinv : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr0]; exact hr'
  have hCk : (C' + 2) * k ≤ C₁ * k := mul_le_mul_of_nonneg_right hC hk0
  have q1 : (r : ℝ) ≤ r ^ 2 := by nlinarith
  have q2 : (r : ℝ) ^ 2 ≤ r ^ 3 := by nlinarith
  have q3 : (r : ℝ) ^ 3 ≤ r ^ 4 := by nlinarith
  nlinarith

end GlobalTheory.Amp
