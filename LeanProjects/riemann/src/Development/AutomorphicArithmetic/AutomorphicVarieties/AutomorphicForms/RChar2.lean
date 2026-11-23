import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

noncomputable section

open Topology
open scoped ContDiff

namespace UpperTheory.V.TR

variable {ι : Type} [Fintype ι]

def expU (z : ι → ℝ) : (ι → ℝ)ˣ :=
  ⟨fun i => Real.exp (z i), fun i => Real.exp (-z i),
    by funext i; simp [← Real.exp_add], by funext i; simp [← Real.exp_add]⟩

omit [Fintype ι] in
@[simp] theorem expU_val (z : ι → ℝ) (i : ι) : (expU z).val i = Real.exp (z i) := rfl

omit [Fintype ι] in

theorem expU_add (z z' : ι → ℝ) : expU (z + z') = expU z * expU z' :=
  Units.ext (funext fun i => Real.exp_add (z i) (z' i))

omit [Fintype ι] in

theorem expU_zero : expU (0 : ι → ℝ) = 1 := Units.ext (funext fun _ => Real.exp_zero)

omit [Fintype ι] in

theorem unit_ne_zero (u : (ι → ℝ)ˣ) (i : ι) : (u : ι → ℝ) i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrFun u.mul_inv i)

omit [Fintype ι] in

theorem exists_sign_mul_expU (u : (ι → ℝ)ˣ) :
    ∃ s : (ι → ℝ)ˣ, s * s = 1 ∧ u = s * expU fun i => Real.log ((u : ι → ℝ) i) := by
  refine ⟨u * (expU fun i => Real.log ((u : ι → ℝ) i))⁻¹, Units.ext (funext fun i => ?_), by simp⟩
  change (u : ι → ℝ) i * Real.exp (-Real.log ((u : ι → ℝ) i)) *
    ((u : ι → ℝ) i * Real.exp (-Real.log ((u : ι → ℝ) i))) = 1
  have h := unit_ne_zero u i
  rw [Real.exp_neg, Real.exp_log_eq_abs h]
  have h2 : |(u : ι → ℝ) i| ≠ 0 := abs_ne_zero.2 h
  field_simp
  rw [sq_abs]

omit [Fintype ι] in

theorem continuous_expU : Continuous (expU : (ι → ℝ) → (ι → ℝ)ˣ) :=
  Units.continuous_iff.2 ⟨continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i),
    continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i).neg⟩

theorem exists_lin (ψ : (ι → ℝ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ L : (ι → ℝ) →L[ℝ] ℂ, ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z) := by
  let f : C(ι → ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z => ⟨(ψ (expU z) : ℂˣ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp continuous_expU)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, expU_zero]))
  have hF' : ∀ z, Complex.exp (F z) = (ψ (expU z) : ℂˣ) := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', expU_add, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

open Classical in

def extZero (ψ : (ι → ℝ)ˣ →* ℂˣ) (x : ι → ℝ) : ℂ := if h : IsUnit x then (ψ h.unit : ℂˣ) else 0

omit [Fintype ι] in

theorem extZero_unit (ψ : (ι → ℝ)ˣ →* ℂˣ) (u : (ι → ℝ)ˣ) : extZero ψ u = (ψ u : ℂˣ) := by
  simp [extZero]

theorem extZero_eventually {ψ : (ι → ℝ)ˣ →* ℂˣ} {L : (ι → ℝ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℝ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℝ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Real.log (x i / (u : ι → ℝ) i)) := by
  have h : ∀ᶠ x in 𝓝 (u : ι → ℝ), ∀ i, 0 < x i / (u : ι → ℝ) i :=
    Filter.eventually_all.2 fun i => ((continuous_apply i).div_const _).continuousAt.eventually_const_lt
      (by beta_reduce; rw [div_self (unit_ne_zero u i)]; exact one_pos)
  filter_upwards [h] with x hx
  have e : x = ((u * expU fun i => Real.log (x i / (u : ι → ℝ) i) : (ι → ℝ)ˣ) : ι → ℝ) := by
    funext i
    change x i = (u : ι → ℝ) i * Real.exp (Real.log (x i / (u : ι → ℝ) i))
    rw [Real.exp_log (hx i), mul_div_cancel₀ _ (unit_ne_zero u i)]
  conv_lhs => rw [e, extZero_unit, map_mul, Units.val_mul, hL]

theorem contDiffAt_extZero (ψ : (ι → ℝ)ˣ →* ℂˣ) (hψ : Continuous ψ) (u : (ι → ℝ)ˣ) :
    ContDiffAt ℝ ∞ (extZero ψ) u := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  refine ContDiffAt.congr_of_eventuallyEq ?_ (extZero_eventually hL u)
  refine contDiffAt_const.mul (ContDiffAt.cexp (L.contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun i => ?_)))
  exact ((contDiffAt_apply ℝ ℝ i _).div_const _).log (by rw [div_self (unit_ne_zero u i)]; exact one_ne_zero)

theorem fderiv_extZero {ψ : (ι → ℝ)ˣ →* ℂˣ} {L : (ι → ℝ) →L[ℝ] ℂ} (hψ : Continuous ψ)
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) : fderiv ℝ (extZero ψ) 1 = L := by
  have h0 : DifferentiableAt ℝ (extZero ψ) 1 := (contDiffAt_extZero ψ hψ 1).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun z : ι → ℝ => fun i => Real.exp (z i)) (ContinuousLinearMap.id ℝ _) 0 := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasFDerivAt (x := 0)).exp
    simpa using this
  have h2 : HasFDerivAt (extZero ψ) (fderiv ℝ (extZero ψ) 1) (fun i : ι => Real.exp ((0 : ι → ℝ) i)) := by
    have : (fun i : ι => Real.exp ((0 : ι → ℝ) i)) = 1 := funext fun _ => Real.exp_zero
    rw [this]; exact h0.hasFDerivAt
  have h3 := h2.comp 0 h1
  have h4 : HasFDerivAt (fun z => Complex.exp (L z)) L 0 := by
    simpa using (L.hasFDerivAt (x := 0)).cexp
  have h5 : (extZero ψ ∘ fun z : ι → ℝ => fun i => Real.exp (z i)) = fun z => Complex.exp (L z) :=
    funext fun z => (extZero_unit ψ (expU z)).trans (hL z)
  rw [h5] at h3
  simpa using h3.unique h4

theorem exists_bound (ψ : (ι → ℝ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (u : (ι → ℝ)ˣ) (B : ℝ), 1 ≤ B → ‖(u : ι → ℝ)‖ ≤ B → ‖((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ)‖ ≤ B →
      ‖((ψ u : ℂˣ) : ℂ)‖ ≤ C * B ^ N := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖L‖
  refine ⟨1, N, zero_le_one, fun u B hB h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hz : ‖fun i => Real.log ((u : ι → ℝ) i)‖ ≤ Real.log B := by
    refine (pi_norm_le_iff_of_nonneg hl).2 fun i => ?_
    rw [← Real.log_abs, ← Real.norm_eq_abs ((u : ι → ℝ) i)]
    refine abs_le.2 ⟨?_, ?_⟩
    · have e : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
        eq_inv_of_mul_eq_one_right (congrFun u.mul_inv i)
      have := Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u⁻¹ i)) ((norm_le_pi_norm _ i).trans h2)
      rw [e, norm_inv, Real.log_inv] at this
      linarith
    · exact Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u i)) ((norm_le_pi_norm _ i).trans h1)
  obtain ⟨s, hs, e⟩ := exists_sign_mul_expU u
  have hs1 : ‖((ψ s : ℂˣ) : ℂ)‖ = 1 := by
    have : ‖((ψ s : ℂˣ) : ℂ)‖ * ‖((ψ s : ℂˣ) : ℂ)‖ = 1 := by
      rw [← norm_mul, ← Units.val_mul, ← map_mul, hs]; simp
    nlinarith [norm_nonneg ((ψ s : ℂˣ) : ℂ)]
  rw [e, map_mul, Units.val_mul, norm_mul, hs1, one_mul, one_mul, hL, Complex.norm_exp]
  have h3 : (L fun i => Real.log ((u : ι → ℝ) i)).re ≤ N * Real.log B :=
    (Complex.re_le_norm _).trans ((L.le_opNorm _).trans (mul_le_mul hN hz (norm_nonneg _) (Nat.cast_nonneg _)))
  refine (Real.exp_le_exp.2 h3).trans_eq ?_
  rw [← Real.log_pow, Real.exp_log (by positivity)]

end UpperTheory.V.TR
