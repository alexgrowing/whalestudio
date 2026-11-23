import Formalism.PeriodIntegrals.DiagRank

noncomputable section

namespace PI.UnitaryGroupMassFormula.DiagRank

open Finset

theorem det_one_sub_p_ne {p : ℕ} [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (1 - (p : ℤ_[p]) • M).det ≠ 0 := by

  intro h0
  have h1 := congrArg (PadicInt.toZMod (p := p)) h0
  rw [RingHom.map_det, map_zero] at h1
  have hI : (PadicInt.toZMod (p := p)).mapMatrix (1 - (p : ℤ_[p]) • M) = 1 := by
    ext i j
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [hI, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem exists_int_mul {p : ℕ} [Fact p.Prime] (D : ℤ) (x : ℚ_[p]) (hx : x ≠ 0 → D < x.valuation) :
    ∃ u : ℤ_[p], x = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hv := hx h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (D + 1) ≠ 0 := zpow_ne_zero _ hp0
  have hnp : ‖(p : ℚ_[p]) ^ (D + 1)‖ = (p : ℝ) ^ (-(D + 1)) := by
    rw [norm_zpow, Padic.norm_p, inv_zpow', zpow_neg]
  refine ⟨⟨x / (p : ℚ_[p]) ^ (D + 1), ?_⟩, ?_⟩
  · rw [norm_div, hnp, Padic.norm_eq_zpow_neg_valuation h0]
    rw [div_le_one (zpow_pos (by linarith) _)]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  · show x = (p : ℚ_[p]) ^ (D + 1) * (x / (p : ℚ_[p]) ^ (D + 1))
    field_simp

open Classical in
theorem diagRank : PI.DiagRank := by
  intro p _ n m X Y c D h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ hp0
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m),
      S = Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D) := ⟨_, rfl⟩
  rw [← hS]
  have hsplit : ∀ a, a ∉ S → ∃ u : ℤ_[p], c a = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
    intro a ha
    apply exists_int_mul D (c a)
    intro hc
    by_contra hle
    exact ha (by rw [hS]; simp [hc, not_lt.mp hle])
  choose! u hu using hsplit

  obtain ⟨s, hs⟩ : ∃ s : Fin m → ℚ_[p], s = fun a => if a ∈ S then c a / (p : ℚ_[p]) ^ D else 0 :=
    ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : Fin m → ℤ_[p], u' = fun a => if a ∈ S then 0 else u a := ⟨_, rfl⟩
  have key : ∀ a, c a = (p : ℚ_[p]) ^ D * s a + (p : ℚ_[p]) ^ (D + 1) * (u' a : ℚ_[p]) := by
    intro a
    by_cases ha : a ∈ S
    · simp [hs, hu', ha]; field_simp
    · simp [hs, hu', ha, hu a ha]
  have hent : ∀ i j, ∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) =
      (if i = j then 1 else 0) - (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by
    intro i j
    have h1 := h i j
    have h2 : ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = (p : ℚ_[p]) ^ D *
        (∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) +
          (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p])) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [key a, zpow_add₀ hp0, zpow_one]
      ring
    have h3 : (if i = j then (p : ℚ_[p]) ^ D else 0) = (p : ℚ_[p]) ^ D * (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h2, h3] at h1
    exact eq_sub_of_add_eq (mul_left_cancel₀ hpD h1)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℤ_[p], N = fun i j => ∑ a, X i a * u' a * Y j a :=
    ⟨_, rfl⟩
  obtain ⟨Xq, hXq⟩ : ∃ Xq : Matrix (Fin n) (Fin m) ℚ_[p], Xq = fun i a => (X i a : ℚ_[p]) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin n) ℚ_[p], B = fun a j => (Y j a : ℚ_[p]) := ⟨_, rfl⟩
  have heq : Xq * Matrix.diagonal s * B = PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N) := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    subst hXq hB
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hent i j, hN]
    show _ = ((_ : ℤ_[p]) : ℚ_[p])
    have hc : ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by
      rw [show ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = PadicInt.Coe.ringHom (∑ a, X i a * u' a * Y j a) from rfl, map_sum]
      rfl
    split_ifs <;> push_cast <;> rw [hc]
  have hdet : (PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N)).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact det_one_sub_p_ne N (Subtype.ext h0)
  have hrank : (Xq * Matrix.diagonal s * B).rank = n := by
    rw [heq, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc n = (Xq * Matrix.diagonal s * B).rank := hrank.symm
    _ ≤ (Xq * Matrix.diagonal s).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal s).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {a // s a ≠ 0} := Matrix.rank_diagonal s
    _ = (Finset.univ.filter (fun a => s a ≠ 0)).card := Fintype.card_subtype _
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro a ha
      by_contra haS
      simp [hs, haS] at ha

end PI.UnitaryGroupMassFormula.DiagRank

end
