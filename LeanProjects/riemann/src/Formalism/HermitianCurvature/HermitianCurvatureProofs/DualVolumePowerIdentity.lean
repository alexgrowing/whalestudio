import Formalism.HermitianCurvature.Statement

namespace Formalism.FourierDecayAlt.P

open Finset Real

namespace Easy

theorem dual_volume_power_identity (ι : Type) [Fintype ι] (c : ι → ℝ) (g rd : ℝ) (r i : ℕ) (hg : 0 < g) (hrd : 0 < rd) :
    (∏ v, c v * (2 * π / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) /
        (g * rd ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(Fintype.card ι : ℤ)) =
      (∏ v, c v) * (2 * π / rd) ^ (((2 * i : ℤ) - 3 - 2 * r) * Fintype.card ι) *
        g ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * Fintype.card ι) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set e : ℤ := (2 * i : ℤ) - 3 - 2 * r with he
  set f : ℤ := (Fintype.card ι : ℤ) with hf
  have h1 : (2 * r : ℤ) + 3 - 2 * i = -e := by rw [he]; ring
  have h2 : ((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) = -e + 1 := by rw [he]; ring
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← zpow_natCast, ← hf]
  have hg0 : g ≠ 0 := hg.ne'
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hpi0 : (2 * π) ≠ 0 := hpi.ne'
  generalize 2 * π = A at hpi0 ⊢
  have k1 : ((A / g) ^ e) ^ f = A ^ (e * f) / g ^ (e * f) := by
    rw [← zpow_mul, div_zpow]
  have k2 : (g * rd ^ (-e)) ^ (-f) = (g ^ f)⁻¹ * rd ^ (e * f) := by
    rw [mul_zpow, ← zpow_mul, zpow_neg, show (-e * -f) = e * f by ring]
  have k3 : (A / rd) ^ (e * f) = A ^ (e * f) / rd ^ (e * f) := div_zpow _ _ _
  have k4 : g ^ ((-e + 1) * f) = (g ^ (e * f))⁻¹ * g ^ f := by
    rw [show ((-e + 1) * f) = -(e * f) + f by ring, zpow_add₀ hg0, zpow_neg]
  rw [k1, k2, k3, k4]
  have : g ^ (e * f) ≠ 0 := zpow_ne_zero _ hg0
  have : g ^ f ≠ 0 := zpow_ne_zero _ hg0
  have : rd ^ (e * f) ≠ 0 := zpow_ne_zero _ hrd0
  field_simp

end Easy

theorem dual_size_identity : Formalism.FourierDecayAlt.DualSizeIdentity := by
  intro ι _ c g rd r i hg hrd
  exact Easy.dual_volume_power_identity ι c g rd r i hg hrd

theorem omega_norm_formula : Formalism.FourierDecayAlt.OmNorm := by
  intro V _ _ ip hadd hsmul hconj z x T T' Dr hT hzz hxx
  have hadd2 : ∀ w x y, ip w (x + y) = ip w x + ip w y := by
    intro w x y
    rw [hconj (x + y) w, hadd, map_add, ← hconj, ← hconj]
  have hsmul2 : ∀ (s : ℂ) w y, ip w (s • y) = starRingEnd ℂ s * ip w y := by
    intro s w y
    rw [hconj (s • y) w, hsmul, map_mul, ← hconj]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set ζ := ip x z with hζ
  have hzx : ip z x = starRingEnd ℂ ζ := hconj x z
  constructor
  · rw [hsmul, hadd, hsmul, hzz]
    field_simp
    ring
  · rw [hsmul, hsmul2, hadd, hadd2, hadd2, hsmul, hsmul, hsmul2, hsmul2, hxx, hzz, hzx, ← hζ]
    apply Complex.ext
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring

end Formalism.FourierDecayAlt.P
