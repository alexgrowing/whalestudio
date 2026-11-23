import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegralStatement

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KExp

theorem norm_cexp_real (t : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * z)‖ = Real.exp (-2 * Real.pi * t * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem uniq (d : ℚ → ℂ) (hwf : (Function.support d).IsWF) (S : Set ℂ)
    (hz : ∀ z ∈ S, HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) 0)
    (z1 : ℂ) (h1 : Summable (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z1)))
    (hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im) : d = 0 := by
  by_contra hne
  have hnon : (Function.support d).Nonempty := by
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hne
    exact ⟨r, hr⟩
  set r0 := hwf.min hnon with hr0def
  have hr0 : d r0 ≠ 0 := hwf.min_mem hnon
  have hle : ∀ r, d r ≠ 0 → r0 ≤ r := fun r hr => hwf.min_le hnon hr
  choose zs hzS hzim using fun j : ℕ => hS (max z1.im 0 + j)
  set y1 := z1.im with hy1
  have hnorm : ∀ (r : ℚ) (z : ℂ), ‖d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * z)‖
      = ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * z.im) := by
    intro r z
    rw [norm_mul]
    have := norm_cexp_real ((r : ℝ) - r0) z
    push_cast at this
    rw [this]
  let f : ℕ → ℚ → ℂ := fun j r => d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * zs j)
  let g : ℚ → ℂ := fun r => if r = r0 then d r0 else 0
  let bound : ℚ → ℝ := fun r => ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * y1)
  have hb : Summable bound := by
    have h2 := ((summable_norm_iff (E := ℂ)).mpr h1).mul_right (Real.exp (2 * Real.pi * r0 * y1))
    refine h2.congr fun r => ?_
    simp only [bound]
    have hn := norm_cexp_real (r : ℝ) z1
    rw [Complex.ofReal_ratCast] at hn
    rw [norm_mul, hn, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop) (f := f) (g := g) hb ?_ ?_
  · have hf0 : ∀ j, ∑' r, f j r = 0 := by
      intro j
      have h := (hz (zs j) (hzS j)).mul_left (Complex.exp (-(2 * Real.pi * Complex.I * (r0 : ℂ) * zs j)))
      rw [mul_zero] at h
      refine Eq.trans (tsum_congr fun r => ?_) h.tsum_eq
      simp only [f]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    have hg : ∑' r, g r = d r0 := by
      rw [tsum_eq_single r0 (fun r hr => by simp [g, hr])]
      simp [g]
    simp only [hf0, hg] at hlim
    exact hr0 (tendsto_nhds_unique hlim tendsto_const_nhds)
  · intro r
    by_cases hr : r = r0
    · subst hr
      simp only [f, g, if_pos rfl, sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      exact tendsto_const_nhds
    by_cases hd : d r = 0
    · simp only [f, g, hd, zero_mul, if_neg hr]
      exact tendsto_const_nhds
    have hlt : (r0 : ℝ) < r := by exact_mod_cast lt_of_le_of_ne (hle r hd) (Ne.symm hr)
    simp only [g, if_neg hr]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpos : 0 < 2 * Real.pi * ((r : ℝ) - r0) := by have := Real.pi_pos; nlinarith
    have hT : Filter.Tendsto (fun j : ℕ => ‖d r‖ * Real.exp (-(2 * Real.pi * ((r : ℝ) - r0) * j))) Filter.atTop (nhds 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hpos)).const_mul ‖d r‖
      simpa using this
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hT
    simp only [f]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (j : ℝ) ≤ (zs j).im := by
      have := hzim j
      have : (0 : ℝ) ≤ max y1 0 := le_max_right _ _
      linarith
    nlinarith
  · refine Filter.Eventually.of_forall fun j r => ?_
    simp only [f, bound]
    rw [hnorm]
    by_cases hd : d r = 0
    · simp [hd]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : (r0 : ℝ) ≤ r := by exact_mod_cast hle r hd
    have : y1 ≤ (zs j).im := by
      have := hzim j
      have : y1 ≤ max y1 0 := le_max_left _ _
      have : (0:ℝ) ≤ j := by positivity
      linarith
    have hp : 0 ≤ 2 * Real.pi * ((r : ℝ) - r0) := mul_nonneg (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left this hp]

end GlobalTheory.KExp

namespace GlobalTheory.KExp

theorem siegel_exp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  intro Ω _ _ _ ε T c M a b hM haM hadm
  classical
  set x : Fin 2 → ℚ := ![(a : ℚ) / M, (b : ℚ) / M] with hx
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a hM haM
  obtain ⟨A', hA', -⟩ := hk b hadm
  have hmem := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hadm
  set f := siegel T c x with hf
  obtain ⟨φ, C, hφ, hsum⟩ := T.an_exp f
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let ι : ℕ → ℚ := fun n => ((k : ℚ) + n) / M
  have hι : Function.Injective ι := by
    intro n m h
    simp only [ι] at h
    rw [div_left_inj' hMq, add_right_inj] at h
    exact_mod_cast h
  let B : ℚ → ℂ := fun r => if h : ∃ n, ι n = r then A' h.choose else 0
  have hBι : ∀ n, B (ι n) = A' n := by
    intro n
    have h : ∃ m, ι m = ι n := ⟨n, rfl⟩
    simp only [B, dif_pos h]
    rw [hι h.choose_spec]
  have hB0 : ∀ r, r ∉ Set.range ι → B r = 0 := by
    intro r hr
    simp only [B]
    rw [dif_neg]
    exact hr
  have hBsum : ∀ z : ℂ, 0 < z.im →
      HasSum (fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (sgC c x z) := by
    intro z hz
    have h2 := (hA' ⟨z, hz⟩).mul_left (ee ((k : ℂ) / M * z))
    rw [← hι.hasSum_iff (fun r hr => by simp [hB0 r hr])]
    have e1 : ((fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) ∘ ι) = fun n : ℕ =>
        ee ((k : ℂ) / M * z) * (A' n * Complex.exp (2 * Real.pi * Complex.I * n * z / M)) := by
      funext n
      simp only [Function.comp_apply, hBι, ι, ee]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
    have e2 : sgC c x z = ee ((k : ℂ) / M * z) * (sg c x ⟨z, hz⟩ * ee (-((k : ℂ) / M) * z)) := by
      simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rw [mul_left_comm, ee, ee, ← Complex.exp_add]
      have : 2 * Real.pi * Complex.I * ((k : ℂ) / M * z) + 2 * Real.pi * Complex.I * (-((k : ℂ) / M) * (z : ℂ)) = 0 := by
        ring
      rw [this, Complex.exp_zero, mul_one]
    rw [e1, e2]
    simpa using h2
  have hgerm : φ =ᶠ[Filter.codiscreteWithin Hs] sgC c x := by
    have := hφ.symm.trans hmem
    exact Filter.Germ.coe_eq.mp this
  let S : Set ℂ := {z | C < z.im ∧ 0 < z.im ∧ φ z = sgC c x z}
  have hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im := by
    intro y
    set Y := max (max y C) 0 + 1 with hY
    set w : ℂ := Complex.I * Y
    have hwim : w.im = Y := by simp [w]
    have hw : w ∈ Hs := by
      show 0 < w.im
      rw [hwim]; have := le_max_right (max y C) 0; linarith
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hgerm w hw
    have h2 : Metric.ball w (1 / 2) ∈ nhdsWithin w {w}ᶜ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by norm_num))
    obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
    have hdist : |z.im - Y| < 1 / 2 := by
      have := Complex.abs_im_le_norm (z - w)
      rw [Metric.mem_ball, dist_eq_norm] at hz2
      rw [Complex.sub_im, hwim] at this
      linarith
    have hyY : y ≤ max (max y C) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hCY : C ≤ max (max y C) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    have h0Y : 0 ≤ max (max y C) 0 := le_max_right _ _
    have hzim : max (max y C) 0 + 1 / 2 < z.im := by
      have := (abs_lt.mp hdist).1; linarith
    have hzH : z ∈ Hs := show 0 < z.im by linarith
    refine ⟨z, ⟨by linarith, by linarith, ?_⟩, by linarith⟩
    rcases hz1 with h | h
    · exact h
    · exact absurd hzH h
  let d : ℚ → ℂ := fun r => ε ((T.exp f).coeff r) - B r
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ S ?_ (Complex.I * (|C| + 1)) ?_ hS
    · have hR : (Set.range ι).IsWF := by
        have : Set.range ι = ι '' Set.univ := Set.image_univ.symm
        rw [this]
        refine (Set.IsPWO.image_of_monotone (Set.isPWO_of_wellQuasiOrderedLE _) ?_).isWF
        intro n m h
        simp only [ι]
        gcongr
      refine ((T.exp f).isWF_support.union hR).mono ?_
      · intro r hr
        by_contra hn
        simp only [Set.mem_union, not_or] at hn
        apply hr
        simp only [d, hB0 r hn.2]
        have : (T.exp f).coeff r = 0 := by simpa [HahnSeries.support] using hn.1
        simp [this]
    · intro z hz
      have := (hsum z hz.1).sub (hBsum z hz.2.1)
      rw [hz.2.2, sub_self] at this
      simpa [d, sub_mul] using this
    · have hzi : C < (Complex.I * (|C| + 1)).im := by
        simp; have := le_abs_self C; linarith
      have hzp : 0 < (Complex.I * (|C| + 1)).im := by simp; positivity
      have := ((hsum _ hzi).summable.sub (hBsum _ hzp).summable)
      simpa [d, sub_mul] using this
  have hdr : ∀ r, ε ((T.exp f).coeff r) = B r := fun r => sub_eq_zero.mp (congrFun hd r)
  refine ⟨k, fun n => (T.exp f).coeff (ι n), ?_, fun n => rfl, ?_⟩
  · have : (fun n => ε ((T.exp f).coeff (ι n))) = A' := funext fun n => by rw [hdr, hBι]
    rw [this]
    exact hA'
  · intro r hr
    have hr' : r ∉ Set.range ι := by
      rintro ⟨n, rfl⟩
      exact hr n rfl
    have := hdr r
    rw [hB0 r hr'] at this
    exact (map_eq_zero_iff ε ε.injective).mp this

end GlobalTheory.KExp
