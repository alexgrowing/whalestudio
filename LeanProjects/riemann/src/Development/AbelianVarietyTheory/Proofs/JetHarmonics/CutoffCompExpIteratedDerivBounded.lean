import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology

theorem cutoff_comp_exp_iteratedDeriv_bounded (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv p (fun t => χ (Real.exp t)) t| ≤ C := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hc : ∀ k t : ℝ, iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
    intro k t
    cases p with
    | zero => simp
    | succ n => simp [iteratedDeriv_succ']
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hs.comp Real.contDiff_exp
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log δ → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have := Real.exp_lt_exp.mpr hs
      rw [Real.exp_log hδ] at this
      simp only [hh, h0 _ this]
    rw [this.iteratedDeriv_eq p, hc]; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, h1 _ this]
    rw [this.iteratedDeriv_eq p, hc]
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log δ) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases lt_or_ge t (Real.log δ) with h1 | h1
  · rw [hlow t h1]; simp
  · rcases lt_or_ge 0 t with h2 | h2
    · rw [hhigh t h2]; split_ifs <;> simp
    · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)

theorem ld_cut_pow_bound (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (e j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  choose B hB0 hB using cutoff_comp_exp_iteratedDeriv_bounded χ hχ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (e : ℝ) ^ (j - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i)) (by positivity), ?_⟩
  intro ε x hε hx
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχ.1.comp Real.contDiff_exp
  unfold LE.ld
  have e1 : (fun u : ℝ => χ (Real.exp u / ε) * Real.exp u ^ e) =
      fun u : ℝ => h (u - Real.log ε) * Real.exp ((e : ℝ) * u) := by
    funext u
    simp only [hh]
    rw [Real.exp_sub, Real.exp_log hε, Real.exp_nat_mul]
  have c1 : ContDiff ℝ j (fun u : ℝ => h (u - Real.log ε)) :=
    (hsm.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have c2 : ContDiff ℝ j (fun u : ℝ => Real.exp ((e : ℝ) * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  beta_reduce
  rw [e1, iteratedDeriv_fun_mul c1.contDiffAt c2.contDiffAt, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedDeriv_comp_sub_const, iteratedDeriv_exp_const_mul]
  beta_reduce
  rw [Real.exp_nat_mul, Real.exp_log hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j.choose i : ℝ)),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (e : ℝ) ^ (j - i) * x ^ e), ← mul_assoc]
  have := hB i (Real.log x - Real.log ε)
  gcongr

theorem ld_cut_pow : ∀ (χ : ℝ → ℝ) (e J : ℕ), C6.IsCut0 χ →
    (∀ ε : ℝ, 0 < ε → CutPow e fun y => χ (y / ε) * y ^ e) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → ∀ j, j ≤ J →
        |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  intro χ e J hχ
  constructor
  · intro ε hε
    obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
    refine ⟨(hs.comp (contDiff_id.div_const ε)).mul (contDiff_id.pow e), ⟨δ * ε, by positivity, fun x hx => ?_⟩,
      1, ε, fun x hx => ?_⟩
    · have : x / ε < δ := by rwa [div_lt_iff₀ hε]
      simp [h0 _ this]
    · have : 1 ≤ x / ε := by rwa [le_div_iff₀ hε, one_mul]
      simp [h1 _ this]
  · choose C hC0 hC using ld_cut_pow_bound χ hχ e
    refine ⟨∑ j ∈ Finset.range (J + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun ε x hε hx j hj => ?_⟩
    refine (hC j ε x hε hx).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))

end GlobalTheory.HatNF
