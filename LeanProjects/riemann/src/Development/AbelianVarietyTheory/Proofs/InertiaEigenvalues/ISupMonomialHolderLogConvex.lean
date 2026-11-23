import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem gA_teichmuller (ρ : ℝ) (y : Formalism.Per.Fl l) :
    gA l ρ (Formalism.Per.tm y) = ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((Formalism.Per.tm y : Formalism.Per.Ainf l).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n = if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0 := by
    intro n
    split_ifs with h
    · subst h
      simp
    · rw [WittVector.teichmuller_coeff_pos l y n (Nat.pos_of_ne_zero h), GlobalTheory.GaussSlope.untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  unfold gA
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0) ≤
      ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := fun n => by split_ifs <;> simp
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0)
      ⟨_, Set.forall_mem_range.2 hall⟩ 0 (by simp))

theorem isGauss_unit_eq_one {ρ : ℝ} (hρ : 0 < ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    {x : Formalism.Per.Acris l} (hx : IsUnit x) : N x = 1 := by
  obtain ⟨h01, -, -, hmul, halg⟩ := hN
  have hl : N (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, halg]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  have h1 : N 1 = 1 := by
    have := hmul (l : Formalism.Per.Acris l) 1
    rw [mul_one, hl] at this
    exact (mul_left_cancel₀ hρ.ne' (this.symm.trans (mul_one ρ).symm))
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h2 := hmul x y
  rw [hy, h1] at h2
  refine le_antisymm (h01 x).2 ?_
  rw [h2]
  exact mul_le_of_le_one_right (h01 x).1 (h01 y).2

theorem gC_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  intro l _ ρ h0 h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  refine ⟨isGauss_unit_eq_one hρ hN isUnit_one, hl, fun c hc => ?_, fun y => ?_,
    fun a ha => isGauss_unit_eq_one hρ hN (ha.map _)⟩
  · have e : zc l c = (l : Formalism.Per.Acris l) ^ c.valuation * zc l (PadicInt.unitCoeff hc : ℤ_[l]) := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [map_mul, map_pow, map_natCast, mul_comm]
    rw [e, GlobalTheory.GaussSlope.map_pow_mul _ hN.2.2.2.1, hl,
      isGauss_unit_eq_one hρ hN ((PadicInt.unitCoeff hc).isUnit.map (zc l)), mul_one]
  · rw [tc, hN.2.2.2.2, gA_teichmuller]

end GlobalTheory.PMon.Gauss

end
