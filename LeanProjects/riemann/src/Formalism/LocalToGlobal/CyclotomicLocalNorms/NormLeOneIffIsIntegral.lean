import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormSubToZModPowVal

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped Classical

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem exists_rat_norm {x : Om l} (hx : x ≠ 0) : ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have h : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / (minpoly ℚ_[l] x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) x
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  rw [h, Padic.norm_eq_zpow_neg_valuation h0, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  field_simp

def vq (x : Om l) : ℚ := if h : x = 0 then 0 else (exists_rat_norm h).choose

theorem norm_eq_rpow {x : Om l} (hx : x ≠ 0) : ‖x‖ = (l : ℝ) ^ (-(vq x : ℝ)) := by
  rw [vq, dif_neg hx]
  exact (exists_rat_norm hx).choose_spec

theorem vq_le_iff {x y : Om l} (hx : x ≠ 0) (hy : y ≠ 0) : vq x ≤ vq y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [norm_eq_rpow hx, norm_eq_rpow hy, Real.rpow_le_rpow_left_iff one_lt_l, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

theorem vq_eq_of_norm {x : Om l} {q : ℚ} (h : ‖x‖ = (l : ℝ) ^ (-(q : ℝ))) : vq x = q := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).ne h
  rw [norm_eq_rpow hx] at h
  have := (Real.rpow_right_inj (by linarith [one_lt_l (l := l)]) (one_lt_l (l := l)).ne').1 h
  exact_mod_cast neg_injective this

theorem vq_mul {x y : Om l} (hx : x ≠ 0) (hy : y ≠ 0) : vq (x * y) = vq x + vq y := by
  apply vq_eq_of_norm
  rw [norm_mul, norm_eq_rpow hx, norm_eq_rpow hy, ← Real.rpow_add (by linarith [one_lt_l (l := l)])]
  congr 1
  push_cast
  ring

def vfun (x : Om l) : WithTop ℚ := if x = 0 then ⊤ else (vq x : WithTop ℚ)

theorem vfun_zero : vfun (0 : Om l) = ⊤ := if_pos rfl

theorem vfun_of_ne {x : Om l} (hx : x ≠ 0) : vfun x = (vq x : WithTop ℚ) := if_neg hx

variable (l) in

def vΩ : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vfun vfun_zero
    (by
      rw [vfun_of_ne one_ne_zero]
      have : vq (1 : Om l) = 0 := vq_eq_of_norm (by simp)
      rw [this]; rfl)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · rw [hxy, vfun_zero]; exact le_top
      rw [vfun_of_ne hx, vfun_of_ne hy, vfun_of_ne hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
        min_le_iff, vq_le_iff hx hxy, vq_le_iff hy hxy]
      exact le_max_iff.1 (PadicAlgCl.isNonarchimedean l x y))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx, vfun_zero]
      by_cases hy : y = 0
      · simp [hy, vfun_zero]
      rw [vfun_of_ne hx, vfun_of_ne hy, vfun_of_ne (mul_ne_zero hx hy), vq_mul hx hy]
      rfl)

theorem vΩ_apply (x : Om l) : vΩ l x = vfun x := rfl

theorem vΩ_of_ne {x : Om l} (hx : x ≠ 0) : vΩ l x = (vq x : WithTop ℚ) := vfun_of_ne hx

theorem le_vΩ_iff (q : ℚ) (x : Om l) : (q : WithTop ℚ) ≤ vΩ l x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  by_cases hx : x = 0
  · subst hx
    rw [vΩ_apply, vfun_zero, norm_zero]
    exact ⟨fun _ => (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).le, fun _ => le_top⟩
  · rw [vΩ_of_ne hx, WithTop.coe_le_coe, norm_eq_rpow hx, Real.rpow_le_rpow_left_iff one_lt_l,
      neg_le_neg_iff]
    exact_mod_cast Iff.rfl

theorem vΩ_eq_iff (q : ℚ) (x : Om l) : vΩ l x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [vΩ_apply, vfun_zero] at h
      exact WithTop.top_ne_coe h
    rw [vΩ_of_ne hx, WithTop.coe_inj] at h
    rw [norm_eq_rpow hx, h]
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at h
      exact (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).ne h
    rw [vΩ_of_ne hx, vq_eq_of_norm h]

theorem norm_l : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem vΩ_l : vΩ l ((l : ℕ) : Om l) = 1 := by
  have : vΩ l ((l : ℕ) : Om l) = ((1 : ℚ) : WithTop ℚ) := by
    rw [vΩ_eq_iff, norm_l]
    simp [Real.rpow_neg_one]
  rw [this]; rfl

theorem zero_le_vΩ_iff (x : Om l) : 0 ≤ vΩ l x ↔ ‖x‖ ≤ 1 := by
  have := le_vΩ_iff 0 x
  simpa using this

variable (l) in

def v (LL : FinExt l) : AddValuation ↥LL.1 (WithTop ℚ) := (vΩ l).comap (algebraMap ↥LL.1 (Om l))

instance towZLL (LL : IntermediateField ℚ_[l] (Om l)) : IsScalarTower ℤ_[l] ↥LL (Om l) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Formalism.L2.LocGap.Gal
