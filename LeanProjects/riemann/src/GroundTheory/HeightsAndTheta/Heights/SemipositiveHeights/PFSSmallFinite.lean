import Mathlib
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StSmallFormsFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FSScaled
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

namespace FSSmallFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem norm_eval_le (c : MRing ι) (k : ℕ) (hc : IsMultiHomog c (fun _ => k)) (z : (Σ κ, ι κ) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) c)‖ ≤
      (∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * (fsH ι).h z ^ k := by
  classical
  have hH : (fsH ι).h z = ∏ κ, ‖WithLp.toLp 2 (fun i => z ⟨κ, i⟩)‖ := by
    simp [fsH, HermLine.ofMetrics, fsMetric]
  have hmon : ∀ μ ∈ c.support, ‖∏ p, z p ^ μ p‖ ≤ (fsH ι).h z ^ k := by
    intro μ hμ
    rw [hH, norm_prod, Fintype.prod_sigma, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun κ _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun κ _ => ?_
    have hk : ∑ i, μ ⟨κ, i⟩ = k := hc μ hμ κ
    rw [← hk, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨κ, i⟩)) i
    rwa [PiLp.toLp_apply] at this
  rw [eval_map, eval₂_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
  rw [norm_mul]
  have hcoef : ‖(Int.castRingHom ℂ) (c.coeff μ)‖ = |((c.coeff μ : ℤ) : ℝ)| := by
    simp [Complex.norm_intCast]
  rw [hcoef]
  exact mul_le_mul_of_nonneg_left (hmon μ hμ) (abs_nonneg _)

theorem fsScaled_h_eq (C : ℝ) (z : (Σ κ, ι κ) → ℂ) :
    (fsScaled ι C).h z = Real.exp (Real.log C) * (fsH ι).h z := by
  simp [fsScaled, HermLine.constShift, HermLine.tensor, HermLine.ofWeight, mul_comm]

end FSSmallFinite

open FSSmallFinite in

theorem FSSmallFinite.proof (hS : SmallFormsFinite.Statement) : FSSmallFinite.Statement := by
  classical
  intro K _ ι _ Ω _ y D hV hB C n

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hV.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    show (X ⟨κ, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  obtain ⟨k, c, hc, hcy, hcond⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof
      K ι Ω y (fun _ => 1) (fun _ => le_rfl) hy hB
  have hc' : IsMultiHomog c (fun _ => k) := fun μ hμ κ => by simpa using hc μ hμ κ
  set e : ℝ := Real.exp (Real.log C) with he
  have he0 : 0 < e := Real.exp_pos _
  set R : ℝ := (∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * e ^ n with hR
  have hfin := hS K ι Ω y D hV (n + k) R
  refine (hfin.preimage (f := fun σ : chartLat y (fsScaled ι C).a n => aeval y c * (σ : Ω))
    fun σ _ τ _ hστ => Subtype.ext (mul_left_cancel₀ hcy hστ)).subset ?_
  intro σ hσ
  refine ⟨?_, fun g hg hgy z hz => ?_⟩
  ·
    have hσNm : (σ : Ω) ∈ chartLatNm y (fun _ => ((1 : ℕ) : ℤ)) n := by
      have key : ∀ s : Ω, s ∈ chartLat y (fsScaled ι C).a n → s ∈ chartLat y (fun _ => ((1 : ℕ) : ℤ)) n := by
        rw [fsScaled_a]
        intro s hs
        simpa using hs
      have h1 := key σ σ.2
      exact fun c' hc' => isIntegral_algebraMap (R := chartRingZ y c') (A := Ω) (x := ⟨_, h1 c' hc'⟩)
    simpa using hcond n σ hσNm
  ·
    have hdeg : ∀ κ, (((fun _ => n + k) : K → ℕ) κ : ℤ) = ((fun _ => k) : K → ℕ) κ + n * (fsScaled ι C).a κ := by
      intro κ
      rw [fsScaled_a]
      push_cast
      ring
    have h1 := hσ (fun _ => n + k) (fun _ => k) g c z hg hc' hdeg (by rw [hgy, mul_comm]) hz
    have h2 := norm_eval_le c k hc' z
    have hH0 : 0 ≤ (fsH ι).h z := ((fsH ι).pos z hz.1).le
    rw [fsScaled_h_eq, mul_pow] at h1
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * (e ^ n * (fsH ι).h z ^ n) := h1
      _ ≤ ((∑ μ ∈ c.support, |((c.coeff μ : ℤ) : ℝ)|) * (fsH ι).h z ^ k) * (e ^ n * (fsH ι).h z ^ n) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = R * (fsH ι).h z ^ (n + k) := by rw [hR, pow_add]; ring

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
