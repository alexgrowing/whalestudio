import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA

noncomputable section

namespace PI.OmFibreUniq.W.SdChar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain

theorem eq_one_of_pow_near (w : ℂ) (hw : ‖w‖ = 1) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1) : w = 1 := by
  have key : ∀ y : ℝ, Real.cos y ≤ 1 / 2 → 1 ≤ ‖Complex.exp (y * Complex.I) - 1‖ := by
    intro y hy
    have hsq : ‖Complex.exp (y * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos y := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
      nlinarith [Real.sin_sq_add_cos_sq y]
    nlinarith [norm_nonneg (Complex.exp (y * Complex.I) - 1)]
  set θ := Complex.arg w with hθ
  have hw' : w = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at this
    simpa using this.symm
  have hpow : ∀ m : ℕ, w ^ m = Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I) := by
    intro m
    rw [hw', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  by_contra hne
  have hθ0 : θ ≠ 0 := by
    intro h0
    apply hne
    rw [hw', h0]
    simp
  have hθb : -Real.pi < θ ∧ θ ≤ Real.pi := ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, Real.pi / 3 ≤ m * |θ| ∧ m * |θ| ≤ Real.pi := by
    have ht : 0 < |θ| := abs_pos.mpr hθ0
    have ht' : |θ| ≤ Real.pi := abs_le.mpr ⟨by linarith [hθb.1], hθb.2⟩
    by_cases hbig : Real.pi / 3 ≤ |θ|
    · exact ⟨1, by simpa using hbig, by simpa using ht'⟩
    · push_neg at hbig
      refine ⟨⌈Real.pi / 3 / |θ|⌉₊, ?_, ?_⟩
      · have := Nat.le_ceil (Real.pi / 3 / |θ|)
        rw [div_le_iff₀ ht] at this
        linarith
      · have h1 := Nat.ceil_lt_add_one (show 0 ≤ Real.pi / 3 / |θ| by positivity)
        have h2 : (⌈Real.pi / 3 / |θ|⌉₊ : ℝ) * |θ| < (Real.pi / 3 / |θ| + 1) * |θ| :=
          mul_lt_mul_of_pos_right h1 ht
        rw [add_mul, div_mul_cancel₀ _ ht.ne'] at h2
        linarith [Real.pi_pos]
  have hcos : Real.cos ((m : ℝ) * θ) ≤ 1 / 2 := by
    have e : Real.cos ((m : ℝ) * θ) = Real.cos ((m : ℝ) * |θ|) := by
      rcases abs_choice θ with h | h <;> rw [h] <;> simp [mul_neg, Real.cos_neg]
    rw [e, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hm2 hm1
  have := h m
  rw [hpow m] at this
  linarith [key _ hcos]

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)

include hψa hψn in
theorem psi_zero : ψ0 0 = 1 := by
  have h := hψa 0 0
  rw [add_zero] at h
  have hne : ψ0 0 ≠ 0 := by
    intro h0
    have := hψn 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : ψ0 0 * (ψ0 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)

include hψa hψn in
theorem psi_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    ψ0 (∑ i ∈ s, f i) = ∏ i ∈ s, ψ0 (f i) := by
  classical
  induction s using Finset.induction_on
  · simp [psi_zero v ψ0 hψa hψn]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, hψa, ih, Finset.prod_insert ha]

include hψa hψn in
theorem psi_natCast_mul (m : ℕ) (t : Fv F v) : ψ0 ((m : Fv F v) * t) = ψ0 t ^ m := by
  induction m with
  | zero => simp [psi_zero v ψ0 hψa hψn]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hψa, ih, pow_succ]

def Aset : Set (Fv F v) := {t | ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1}

include hψc hψa hψn in
theorem Aset_mem_nhds : Aset v ψ0 ∈ 𝓝 (0 : Fv F v) := by
  have h0 : ψ0 0 = 1 := psi_zero v ψ0 hψa hψn
  have hU : {x | ‖ψ0 x - 1‖ < 1} ∈ 𝓝 (0 : Fv F v) := by
    apply (isOpen_lt (hψc.sub continuous_const).norm continuous_const).mem_nhds
    simp [h0]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  apply Filter.mem_of_superset (Valued.mem_nhds_zero.mpr ⟨γ, subset_rfl⟩)
  intro t ht c hc
  have hin : ∀ c' ∈ v.adicCompletionIntegers F, ‖ψ0 (c' * t) - 1‖ < 1 := by
    intro c' hc'
    apply hγ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valuation.restrict_le_one_iff] at hc'
    simp only [Set.mem_setOf_eq, map_mul]
    calc Valued.v.restrict c' * Valued.v.restrict t ≤ 1 * Valued.v.restrict t := by gcongr
      _ = Valued.v.restrict t := one_mul _
      _ < _ := ht
  apply eq_one_of_pow_near _ (hψn _)
  intro m
  rw [← psi_natCast_mul v ψ0 hψa hψn, ← mul_assoc]
  exact hin _ (mul_mem (natCast_mem _ m) hc)

include hψa hψn in
theorem Aset_bdd (hnt : ∃ y, ψ0 y ≠ 1) :
    ∃ y0 : Fv F v, y0 ≠ 0 ∧ ∀ t ∈ Aset v ψ0, ∃ s ∈ v.adicCompletionIntegers F, t = y0 * s := by
  obtain ⟨y, hy⟩ := hnt
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (psi_zero v ψ0 hψa hψn)
  refine ⟨y, hy0, fun t ht => ⟨t / y, ?_, by field_simp⟩⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases ht0 : t = 0
  · simp [ht0]
  rcases le_total (Valued.v (t / y)) 1 with hle | hge
  · exact hle
  · exfalso
    apply hy
    have hne : Valued.v (t / y) ≠ 0 := (Valuation.ne_zero_iff _).2 (div_ne_zero ht0 hy0)
    have hc : y / t ∈ v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← inv_div, map_inv₀]
      calc (Valued.v (t / y))⁻¹ = (Valued.v (t / y))⁻¹ * 1 := (mul_one _).symm
        _ ≤ (Valued.v (t / y))⁻¹ * Valued.v (t / y) := by gcongr
        _ = 1 := inv_mul_cancel₀ hne
    have := (show ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1 from ht) _ hc
    rwa [div_mul_cancel₀ _ ht0] at this

end PI.OmFibreUniq.W.SdChar
