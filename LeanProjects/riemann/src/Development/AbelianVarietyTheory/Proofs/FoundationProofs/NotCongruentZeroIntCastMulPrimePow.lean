import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IntNorm

theorem norm_intCast_qbar (l : ℕ) [Fact l.Prime] (d : ℤ) :
    ‖(d : Qbar l)‖ = ‖(d : ℚ_[l])‖ := by
  have h : (d : Qbar l) = ((d : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends]

theorem norm_l_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem not_cg_int_mul_pow (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hlt : |d| < (l : ℤ) ^ t) : ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  intro h
  unfold Cg at h
  rw [sub_zero, norm_mul, norm_pow, norm_pow, pow_add] at h
  have hlpos : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ := by
    rw [norm_l_qbar]; have := (Fact.out : l.Prime).pos; positivity
  have hk : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ ^ k := pow_pos hlpos k
  have h1 : ‖(d : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ t := le_of_mul_le_mul_right h hk
  rw [norm_intCast_qbar, norm_l_qbar] at h1
  have h2 : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have h3 : ((l : ℤ) ^ t) ∣ d := (Padic.norm_int_le_pow_iff_dvd d t).mp h2
  have h4 : ((l : ℤ) ^ t) ≤ |d| := by
    have := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr h3)
    exact this
  omega

end GlobalTheory.Ord2.IntNorm
