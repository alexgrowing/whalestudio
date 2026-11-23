import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem tE_eq_one_of_mem_middle_block (μ : ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tE μ k r i = 1 := by
  unfold Formalism.L2.SG.Pf.Choice.tE
  rw [if_neg (by omega), if_neg (by omega)]

theorem torS_apply (μ : ℂ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (torS μ k r * m * torS μ⁻¹ k r) i j = tE μ k r i * m i j * tE μ⁻¹ k r j := by
  have e1 : torS μ k r = Matrix.diagonal (tE μ k r) := rfl
  have e2 : torS μ⁻¹ k r = Matrix.diagonal (tE μ⁻¹ k r) := rfl
  rw [e1, e2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tor_comm (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : torS μ k r * h = h * torS μ k r := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [torS_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · rw [tE_eq_one_of_mem_middle_block μ i (by omega) (by omega), tE_eq_one_of_mem_middle_block μ j (by omega) (by omega), one_mul, mul_one]

theorem tor_conj_uw {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    torS μ k r * h * torS μ⁻¹ k r = h := by
  rw [tor_comm μ hh, Matrix.mul_assoc, torS_mul_inv μ hμ, Matrix.mul_one]

theorem tor_mulVec_wb (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : torS μ k r *ᵥ z = z := by
  funext i
  rw [show torS μ k r = Matrix.diagonal (tE μ k r) from rfl, Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · push_neg at h
    rw [tE_eq_one_of_mem_middle_block μ i h.1 h.2, one_mul]

theorem ell_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (torS μ k r * m * torS μ⁻¹ k r) = μ * ell k r z m := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [torS_apply, tE_eI, show eI k r ⟨a.val + 1, ha⟩ = eI k r ⟨a.val + 1, ha⟩ from rfl, tE_eI]
    simp only []
    have e : r - (a : ℕ) = (r - ((a : ℕ) + 1)) + 1 := by omega
    rw [e, pow_succ, inv_pow]
    field_simp
  · have hv : (torS μ k r * m * torS μ⁻¹ k r) *ᵥ z = torS μ k r *ᵥ (m *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tor_mulVec_wb μ⁻¹ hz]
    rw [hv, torS_eq, Matrix.mulVec_diagonal, tE_eI]
    have e : r - (a : ℕ) = 1 := by have := a.isLt; omega
    rw [e, pow_one]

theorem psi_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c (torS μ k r * m * torS μ⁻¹ k r) = psi k r z (c * μ) m := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_tor hμ hz m, ← mul_assoc]

theorem tor_mem_UH {μ : ℂ} (hμ : μ ≠ 0) : torS μ k r ∈ UH (Hpk k r) := torS_gram μ hμ

theorem UH_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

theorem tor_conj_N {μ : ℂ} (hμ : μ ≠ 0) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : torS μ k r * a * torS μ⁻¹ k r ∈ Nset k r := by
  obtain ⟨hU, hc1, hc2⟩ := ha
  refine ⟨UH_mul (UH_mul (tor_mem_UH hμ) hU) (tor_mem_UH (inv_ne_zero hμ)), fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [torS_apply, hc1 b i hbi]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp
  · rw [torS_apply, hc2 i j h1 h2 h3]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp

end Formalism.L2.SG.RealObj.EnergyIntTor
