import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.F

namespace Taylor

open PowerSeries

theorem coeff_taylor0 (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylor0 f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  simp [taylor0]

theorem taylor0_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g := by
  ext n
  rw [map_add, coeff_taylor0, coeff_taylor0, coeff_taylor0,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylor0_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z * g z) = taylor0 f * taylor0 g := by
  ext n
  rw [coeff_mul, coeff_taylor0, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_taylor0]
  have h1 : (n.factorial : ℂ) = (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi').symm
  have h2 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  have h3 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h4 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  rw [h1]
  field_simp

theorem taylor0_const (c : ℂ) : taylor0 (fun _ => c) = C c := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem taylor0_id : taylor0 (fun z => z) = X := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_fun_id_zero, coeff_X]
  split_ifs with h
  · simp [h]
  · simp

theorem taylor0_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : taylor0 f = taylor0 g := by
  ext n
  rw [coeff_taylor0, coeff_taylor0, h.iteratedDeriv_eq]

theorem taylor0_deriv (f : ℂ → ℂ) : taylor0 (deriv f) = derivative ℂ (taylor0 f) := by
  ext n
  rw [coeff_derivative, coeff_taylor0, coeff_taylor0, ← iteratedDeriv_succ', Nat.factorial_succ]
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp

theorem iteratedDeriv_comp_mul (a : ℂ) (n : ℕ) : ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 →
    iteratedDeriv n (fun z => f (a * z)) 0 = a ^ n * iteratedDeriv n f 0 := by
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have hc : Filter.Tendsto (fun z : ℂ => a * z) (nhds 0) (nhds 0) := by
      have : Continuous fun z : ℂ => a * z := by fun_prop
      simpa using this.tendsto 0
    have he : deriv (fun z => f (a * z)) =ᶠ[nhds 0] fun z => a * deriv f (a * z) := by
      filter_upwards [hc.eventually hf.eventually_analyticAt] with z hz
      have h1 : HasDerivAt f (deriv f (a * z)) (a * z) := hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun z : ℂ => a * z) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      have := (h1.comp z h2).deriv
      rw [mul_comm] at this
      exact this
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq, iteratedDeriv_const_mul_field, ih _ hf.deriv,
      iteratedDeriv_succ', pow_succ]
    ring

theorem taylor0_rescale {f : ℂ → ℂ} (a : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylor0 (fun z => f (a * z)) = rescale a (taylor0 f) := by
  ext n
  rw [coeff_rescale, coeff_taylor0, coeff_taylor0, iteratedDeriv_comp_mul a n f hf, mul_div_assoc]

theorem taylor0_inj {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : taylor0 f = taylor0 g) : f =ᶠ[nhds 0] g := by
  have hd : AnalyticAt ℂ (fun z => f z - g z) 0 := hf.fun_sub hg
  have h0 : ∀ n, iteratedDeriv n (fun z => f z - g z) 0 = 0 := by
    intro n
    have h1 := congrArg (coeff n) h
    rw [coeff_taylor0, coeff_taylor0] at h1
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
      field_simp at h1
      exact h1
    rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, h2, sub_self]
  have ht : analyticOrderAt (fun z => f z - g z) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mpr fun i _ => h0 i
  rw [analyticOrderAt_eq_top] at ht
  filter_upwards [ht] with z hz
  exact sub_eq_zero.mp hz

theorem ode_zero {a Y : PowerSeries ℂ} (h : derivative ℂ Y = a * Y) (h0 : constantCoeff Y = 0) :
    Y = 0 := by
  have key : ∀ n, coeff n Y = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
        have h1 := congrArg (coeff n) h
        rw [coeff_derivative, coeff_mul] at h1
        have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 a * coeff p.2 Y = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have : p.2 < n + 1 := by
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
            omega
          rw [ih _ this, mul_zero]
        rw [h2] at h1
        have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
        exact (mul_eq_zero.mp h1).resolve_right h4
  ext n
  simpa using key n

theorem taylor0_exp {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    taylor0 (fun z => Complex.exp (f z)) = Formalism.L2.Th1.B.fExp (taylor0 f) := by
  have hE : AnalyticAt ℂ (fun z => Complex.exp (f z)) 0 := hf.cexp
  have hc : constantCoeff (taylor0 f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have hS : HasSubst (taylor0 f) := HasSubst.of_constantCoeff_zero' hc
  have he : deriv (fun z => Complex.exp (f z)) =ᶠ[nhds 0] fun z => deriv f z * Complex.exp (f z) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    have := (hz.differentiableAt.hasDerivAt.cexp).deriv
    rw [mul_comm] at this
    exact this
  have h1 : derivative ℂ (taylor0 fun z => Complex.exp (f z))
      = derivative ℂ (taylor0 f) * taylor0 fun z => Complex.exp (f z) := by
    rw [← taylor0_deriv, taylor0_congr he, taylor0_mul hf.deriv hE, taylor0_deriv]
  have h2 : derivative ℂ (Formalism.L2.Th1.B.fExp (taylor0 f))
      = derivative ℂ (taylor0 f) * Formalism.L2.Th1.B.fExp (taylor0 f) := by
    unfold Formalism.L2.Th1.B.fExp
    rw [derivative_subst hS, derivative_exp, mul_comm]
  have h3 : constantCoeff (taylor0 fun z => Complex.exp (f z)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have h4 : constantCoeff (Formalism.L2.Th1.B.fExp (taylor0 f)) = 1 := by
    unfold Formalism.L2.Th1.B.fExp
    have h5 : exp ℂ = 1 + (exp ℂ - 1) := by ring
    have h6 : (1 : PowerSeries ℂ).subst (taylor0 f) = (1 : PowerSeries ℂ) := by
      rw [← coe_substAlgHom hS, map_one]
    have h7 : constantCoeff ((exp ℂ - 1).subst (taylor0 f) : PowerSeries ℂ) = 0 :=
      constantCoeff_subst_eq_zero hc _ (by simp)
    rw [h5, subst_add hS, h6, map_add, map_one, h7, add_zero]
  refine sub_eq_zero.mp (ode_zero (a := derivative ℂ (taylor0 f)) ?_ ?_)
  · rw [map_sub, h1, h2, mul_sub]
  · rw [map_sub, h3, h4, sub_self]

end Taylor

theorem taylor_ring : TaylorRing :=
  ⟨fun _ _ hf hg => ⟨Taylor.taylor0_add hf hg, Taylor.taylor0_mul hf hg⟩, Taylor.taylor0_const,
    Taylor.taylor0_id, fun _ _ h => Taylor.taylor0_congr h⟩

theorem taylor_deriv : TaylorDeriv :=
  ⟨fun f _ => Taylor.taylor0_deriv f, fun _ a hf => Taylor.taylor0_rescale a hf,
    fun _ _ hf hg h => Taylor.taylor0_inj hf hg h⟩

theorem taylor_exp : TaylorExp := fun _ hf h0 => Taylor.taylor0_exp hf h0

end Formalism.L2.Th1.F
