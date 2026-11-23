import Mathlib
import GroundTheory.GlobalFields.TateThesis.ArchChars

namespace GroundTheory.Global

open Complex

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (u : ℂ) :
    (r : ℂ) ^ u = Complex.exp (u * (Real.log r : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    mul_comm]

theorem existsUnique_cpow_of_pos (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  let e : ℝ → {x : ℝ // 0 < x} := fun t => ⟨Real.exp t, Real.exp_pos t⟩
  have econt : Continuous e := Real.continuous_exp.subtype_mk _
  have hlog : ∀ x : {x : ℝ // 0 < x}, e (Real.log x) = x :=
    fun x => Subtype.ext (Real.exp_log x.2)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Subtype.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  refine ⟨s, fun x => ?_, fun s' h' => eq_of_forall_exp_mul_eq fun t => ?_⟩
  · rw [ofReal_cpow_eq_exp x.2, ← hs', hlog]
  · have h1 := h' (e t)
    rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
    rw [← h1, hs']

theorem existsUnique_realUnits (χ : ℝˣ →ₜ* ℂˣ) :
    ∃! p : Fin 2 × ℂ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2 := by
  let e : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  have econt : Continuous e := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  have hpos : ∀ (r : ℝ) (hr : 0 < r), (χ (Units.mk0 r hr.ne') : ℂ) = (r : ℂ) ^ s := by
    intro r hr
    have : Units.mk0 r hr.ne' = e (Real.log r) := Units.ext (Real.exp_log hr).symm
    rw [this, hs', ofReal_cpow_eq_exp hr]

  set c : ℂ := (χ (-1) : ℂ) with hc
  have hcc : c * c = 1 := by
    rw [hc, ← Units.val_mul, ← map_mul]
    simp
  let a : Fin 2 := if c = 1 then 0 else 1
  have ha : c = (-1 : ℂ) ^ (a : ℕ) := by
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · simp [a, h]
    · have hne : (-1 : ℂ) ≠ 1 := by norm_num
      simp [a, h, hne]
  have hneg1 : ∀ x : ℝˣ, x = -1 * Units.mk0 (-(x : ℝ)) (neg_ne_zero.mpr x.ne_zero) := by
    intro x
    ext
    simp
  refine ⟨(a, s), fun x => ?_, ?_⟩
  · rcases lt_or_gt_of_ne x.ne_zero with hx | hx
    · conv_lhs => rw [hneg1 x]
      rw [map_mul, Units.val_mul, ← hc, hpos _ (neg_pos.mpr hx), ha, Real.sign_of_neg hx, abs_of_neg hx]
      push_cast
      ring
    · have : x = Units.mk0 (x : ℝ) hx.ne' := by ext; simp
      conv_lhs => rw [this]
      rw [hpos _ hx, Real.sign_of_pos hx, abs_of_pos hx]
      simp
  · rintro ⟨a', s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℝˣ) : ℝ) = Real.exp t := rfl
      rw [he, Real.sign_of_pos (Real.exp_pos t), abs_of_pos (Real.exp_pos t),
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      simp only [Complex.ofReal_one, one_pow, one_mul] at h1
      rw [← h1, hs']
    have ha' : (-1 : ℂ) ^ (a' : ℕ) = (-1 : ℂ) ^ (a : ℕ) := by
      have h1 := h' (-1)
      simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one, Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num)] at h1
      rw [← ha, hc, h1]
      push_cast
      ring
    have haa : a' = a := by
      revert ha'
      generalize a = b
      fin_cases a' <;> fin_cases b <;> norm_num
    simp [haa, hs's]

theorem existsUnique_circle_zpow (χ : Circle →ₜ* ℂˣ) :
    ∃! m : ℤ, ∀ z : Circle, (χ z : ℂ) = (z : ℂ) ^ m := by
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (Circle.exp t))
    (χ.continuous.comp Circle.exp.continuous)
    (fun a b => by simp only [Circle.exp_add, map_mul])
  have hs' : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn⟩ : ∃ n : ℤ, s = n * I := by
    have h1 : Complex.exp (s * (2 * Real.pi : ℝ)) = 1 := by
      rw [← hs', Circle.exp_two_pi, map_one, Units.val_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  have hval : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = (Circle.exp t : ℂ) ^ n := by
    intro t
    rw [hs', Circle.coe_exp, ← Complex.exp_int_mul, hn]
    congr 1
    ring
  refine ⟨n, fun z => ?_, fun m hm => ?_⟩
  · rw [← Circle.exp_arg z, hval]
  · have hmn : (m : ℂ) * I = n * I := eq_of_forall_exp_mul_eq fun t => by
      have h1 := hm (Circle.exp t)
      rw [hval, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_int_mul] at h1
      calc Complex.exp (m * I * t) = Complex.exp (m * (t * I)) := by ring_nf
        _ = Complex.exp (n * (t * I)) := h1.symm
        _ = Complex.exp (n * I * t) := by ring_nf
    exact_mod_cast mul_right_cancel₀ I_ne_zero hmn

noncomputable def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_subtype_val.congr fun _ => rfl)

@[simp] theorem coe_circleToUnits (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z := rfl

theorem existsUnique_complexUnits (χ : ℂˣ →ₜ* ℂˣ) :
    ∃! p : ℤ × ℂ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2 := by

  let e : ℝ → ℂˣ := fun t => Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast (Real.exp_pos t).ne')
  have econt : Continuous e :=
    Units.isEmbedding_val₀.continuous_iff.mpr (Complex.continuous_ofReal.comp Real.continuous_exp)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (by simp [e, Complex.exp_add]))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn, hnu⟩ := existsUnique_circle_zpow (χ.comp circleToUnits)
  have hn' : ∀ w : Circle, (χ (circleToUnits w) : ℂ) = (w : ℂ) ^ n := hn
  have hnorm : ∀ z : ℂˣ, 0 < ‖(z : ℂ)‖ := fun z => norm_pos_iff.mpr z.ne_zero
  refine ⟨(n, s), fun z => ?_, ?_⟩
  · have hz : z = e (Real.log ‖(z : ℂ)‖) * circleToUnits (Circle.exp (Complex.arg z)) := by
      ext
      rw [Units.val_mul, coe_circleToUnits, Circle.coe_exp]
      show (z : ℂ) = (Real.exp (Real.log ‖(z : ℂ)‖) : ℂ) * _
      rw [Real.exp_log (hnorm z), Complex.norm_mul_exp_arg_mul_I]
    have hw : (Circle.exp (Complex.arg z) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
      rw [Circle.coe_exp, eq_div_iff (by exact_mod_cast (hnorm z).ne'), mul_comm,
        Complex.norm_mul_exp_arg_mul_I]
    conv_lhs => rw [hz]
    rw [map_mul, Units.val_mul, hs', hn', hw, ofReal_cpow_eq_exp (hnorm z), mul_comm]
  · rintro ⟨m, s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℂˣ) : ℂ) = (Real.exp t : ℂ) := rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
        div_self (by exact_mod_cast (Real.exp_pos t).ne'), one_zpow, one_mul,
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      rw [← h1, hs']
    have hmn : m = n := hnu m fun w => by
      have h1 := h' (circleToUnits w)
      rw [coe_circleToUnits, Circle.norm_coe] at h1
      simpa using h1
    simp [hmn, hs's]

end GroundTheory.Global
