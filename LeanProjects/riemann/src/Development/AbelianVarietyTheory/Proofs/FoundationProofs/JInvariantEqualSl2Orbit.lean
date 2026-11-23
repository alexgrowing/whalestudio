import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantHomothety

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.JOrbit

open GroundTheory.Global.Elliptic

theorem exists_smul_of_homothetic (τ σ : ℍ) {c : ℂ} (hc : c ≠ 0)
    (h : ((latticeOfTau τ).lattice : Set ℂ) = (c * ·) '' (latticeOfTau σ).lattice) :
    ∃ γ : SL(2, ℤ), τ = γ • σ := by
  have m1 : (τ : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₁_mem_lattice
  have m2 : (1 : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₂_mem_lattice
  have m3 : c * σ ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨σ, (latticeOfTau σ).ω₁_mem_lattice, rfl⟩
  have m4 : c * 1 ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨1, (latticeOfTau σ).ω₂_mem_lattice, rfl⟩
  obtain ⟨z, hz, h1⟩ := m1
  obtain ⟨w, hw, h2⟩ := m2
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  obtain ⟨e, f, rfl⟩ := PeriodPair.mem_lattice.1 hw
  obtain ⟨p, q, h3⟩ := PeriodPair.mem_lattice.1 m3
  obtain ⟨r, s, h4⟩ := PeriodPair.mem_lattice.1 m4
  simp only [latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one] at h1 h2 h3 h4
  have k1 : (σ : ℂ) = p * (a * σ + b) + q * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h3 - p * h1 - q * h2
  have k2 : (1 : ℂ) = r * (a * σ + b) + s * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h4 - r * h1 - s * h2
  have k3 : (τ : ℂ) * (e * σ + f) = a * σ + b := by
    apply mul_left_cancel₀ hc
    linear_combination (τ : ℂ) * h2 - h1
  have hy : 0 < σ.im := σ.im_pos
  have hv : 0 < τ.im := τ.im_pos
  have k1i := congrArg Complex.im k1
  have k1r := congrArg Complex.re k1
  have k2i := congrArg Complex.im k2
  have k2r := congrArg Complex.re k2
  have k3i := congrArg Complex.im k3
  have k3r := congrArg Complex.re k3
  simp at k1i k1r k2i k2r k3i k3r
  have e1 : ((p * a + q * e : ℤ) : ℝ) = (1 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k1i
  have e3 : ((r * a + s * e : ℤ) : ℝ) = (0 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k2i
  have e2 : ((p * b + q * f : ℤ) : ℝ) = (0 : ℤ) := by
    push_cast at e1 ⊢; linear_combination -k1r - σ.re * e1
  have e4 : ((r * b + s * f : ℤ) : ℝ) = (1 : ℤ) := by
    push_cast at e3 ⊢; linear_combination -k2r - σ.re * e3
  have e1' : p * a + q * e = 1 := by exact_mod_cast e1
  have e2' : p * b + q * f = 0 := by exact_mod_cast e2
  have e3' : r * a + s * e = 0 := by exact_mod_cast e3
  have e4' : r * b + s * f = 1 := by exact_mod_cast e4
  have hdet : (a * f - b * e) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * f) * e1' + e4' - (r * a + s * e) * e2'
  have him : τ.im * ((e * σ.re + f) ^ 2 + (e * σ.im) ^ 2) = σ.im * ((a * f - b * e : ℤ) : ℝ) := by
    push_cast
    linear_combination (e * σ.re + f) * k3i - (e * σ.im) * k3r
  have hnn : (0 : ℝ) ≤ ((a * f - b * e : ℤ) : ℝ) := by
    have : 0 ≤ σ.im * ((a * f - b * e : ℤ) : ℝ) := by rw [← him]; positivity
    exact (mul_nonneg_iff_of_pos_left hy).1 this
  have hnn' : 0 ≤ a * f - b * e := by exact_mod_cast hnn
  have hD : a * f - b * e = 1 := Int.eq_one_of_mul_eq_one_right hnn' hdet
  have hne : (e : ℂ) * σ + f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  let γ : SL(2, ℤ) := ⟨!![a, b; e, f], by rw [Matrix.det_fin_two_of]; exact hD⟩
  refine ⟨γ, ?_⟩
  ext
  rw [coe_specialLinearGroup_apply γ σ]
  simp [γ]
  rw [eq_div_iff hne, k3]

theorem exists_smul_of_E₄_E₆ :
    ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  intro τ σ h
  have hj : modularJ σ = modularJ τ := by
    have h1 := ModularForm.discriminant_ne_zero τ
    have h2 := ModularForm.discriminant_ne_zero σ
    rw [modularJ, modularJ, div_eq_div_iff h2 h1,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq σ]
    linear_combination h / 1728
  obtain ⟨c, hc, hl⟩ := (modularJ_eq_iff σ τ).1 hj
  exact exists_smul_of_homothetic τ σ hc hl

end GlobalTheory.JOrbit
