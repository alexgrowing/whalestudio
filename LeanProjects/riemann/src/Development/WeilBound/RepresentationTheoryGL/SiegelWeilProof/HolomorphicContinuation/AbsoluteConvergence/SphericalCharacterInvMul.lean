import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem first_cayley_block_one (n : ℕ) : u1 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u1, h21, h22]

theorem second_cayley_block_one (n : ℕ) : u2 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u2, h21, h22]

theorem weight_factor_one (n p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  show det (1 : M2 n) ^ e * f0 p q (1 : M2 n) = 1
  simp [f0, first_cayley_block_one, second_cayley_block_one]

theorem spherical_character_inv_mul (hM : Mult) (n p q : ℕ) (e : ℤ) (k : GR n) (hk : k ∈ KR n) :
    F0 p q e k⁻¹ * F0 p q e k = 1 := by
  rw [← ((hM n p q e).1 k⁻¹ k hk).1, inv_mul_cancel, weight_factor_one]

theorem sph (hI : Iwa) (hM : Mult) : Sph := by
  intro n p q e _ _ μ _ _ y z
  obtain ⟨b, k0, hb, hk0, rfl⟩ := hI n y
  have hmul := (hM n p q e).1
  have hup := (hM n p q e).2
  have step1 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (b * k0 * (k : GR n) * z)
      = F0 p q e b * ((F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z)) := by
    intro k
    rw [show b * k0 * (k : GR n) * z = b * (k0 * (k : GR n) * z) by simp only [mul_assoc],
      (hup b _ hb).1]
    ring
  simp_rw [step1]
  rw [integral_const_mul, (hmul b k0 hk0).1, mul_assoc]
  congr 1
  let k0' : KR n := ⟨k0, hk0⟩
  let f : KR n → ℂ := fun k' => (F0 p q e (k0⁻¹ * (k' : GR n)))⁻¹ * F0 p q e ((k' : GR n) * z)
  have h1 : ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z) ∂μ
      = ∫ k : KR n, f (k0' * k) ∂μ := by
    congr 1
    ext k
    show _ = (F0 p q e (k0⁻¹ * (k0 * (k : GR n))))⁻¹ * F0 p q e (k0 * (k : GR n) * z)
    rw [inv_mul_cancel_left]
  rw [h1, integral_mul_left_eq_self f k0']
  have h2 : ∀ k' : KR n, f k' = F0 p q e k0 * ((F0 p q e (k' : GR n))⁻¹ * F0 p q e ((k' : GR n) * z)) := by
    intro k'
    simp only [f]
    rw [(hmul k0⁻¹ k' k'.2).1, mul_inv,
      inv_eq_of_mul_eq_one_right (spherical_character_inv_mul hM n p q e k0 hk0)]
    ring
  simp_rw [h2]
  rw [integral_const_mul]

end PositivityTheory.Rg.Sw.AbsSt
