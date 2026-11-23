import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KapMulLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryTubeProductChartHasStrictFDerivAtEntryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RotationInvariantMeasureUnitCircleArcStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThinUnitaryTubeVolumeLimitArithStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Tube

theorem unrealify_cont {m : ℕ} : Continuous (unrealify (m := m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => (x (i, j, false) : ℂ) + (x (i, j, true) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [unrealify]
  rw [this]; fun_prop

theorem chart_zero (k : ℕ) (η : ℝ) : chart η (0 : Par k) = 1 := by
  have h1 : unrealify (m := k) (0 : EuclideanSpace ℝ _) = 0 := by
    ext i j; apply Complex.ext <;> simp [unrealify]
  have h2 : hv (0 : EuclideanSpace ℂ (Fin k)) = 0 := by funext j; simp [hv]
  simp [chart, h1, h2, kap_one, sec_zero]

theorem thin_tube : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∀ (μ : Measure (PI.MtM (k + 1))) (μ₀ : Measure (PI.MtM k)) (c c₀ : ℝ), 0 < c → 0 < c₀ → PI.IsHaarOnM (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ → HasDens (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ (ENNReal.ofReal c) → PI.IsHaarOnM (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ → μ₀ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ (ENNReal.ofReal c₀) → Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  intro k η hk hη μ μ₀ c c₀ hc hc₀ hμ hd hμ₀ h1 hd₀
  change PI.IsHaarOnM (UH (Hd k η)) μ at hμ
  change HasDens (UH (Hd k η)) μ _ at hd
  have hexp : ∀ X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)),
      NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _)) ∈ UH (1 : Matrix (Fin k) (Fin k) ℂ) := fun X =>
    CCRuleCW.exp_mem_UH _ _ ((GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive k 1 X.1 (Matrix.one_mul _)).1 X.2)
  obtain ⟨L, hL, hvol⟩ := GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume k η hk hη
  have hmem : ∀ᶠ x in 𝓝 (0 : Par k), chart η x ∈ UH (Hd k η) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par k) one_pos] with x hx
    have hw : ‖x.2.2‖ < 1 := ((norm_snd_le x.2).trans (norm_snd_le x)).trans_lt (mem_ball_zero_iff.1 hx)
    refine (comp hη (hexp x.1) (Complex.norm_exp_ofReal_mul_I x.2.1) ?_).1
    rw [nsq_hv]; have := norm_nonneg x.2.2; nlinarith
  have hch := GlobalTheory.T.tendsto_measure_image_ball_div_volume (k + 1) (UH (Hd k η)) μ _ (GlobalTheory.GramExp.isMatGroup_UH _ (Hd_sq k hη)) hμ hd (Par k)
    (chart η) L (chart_zero k η) hmem (fun i j => by
      obtain ⟨D, h, h'⟩ := GlobalTheory.T.unitaryTubeProductChart_hasStrictFDerivAt_entry k η i j
      exact ⟨D, h, fun v => by rw [h', hL]⟩)
  refine GlobalTheory.T.thinUnitaryTube_volume_limit_arith k c c₀ (fun t => μ (tubeO k η t)) _
    (fun ρ => μ₀ (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)))
    (fun ρ => volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ)) hc hc₀ (fun t s ht hs => ⟨?_, ?_⟩)
    (fun ρ hρ => ⟨Metric.measure_ball_pos _ _ hρ, measure_ball_lt_top⟩) hd₀ (hch.congr' ?_)
  · refine measure_mono fun g hg => ?_
    exact (abs_id hη hg.1).le.trans hg.2.le
  · refine measure_mono_ae ?_
    have : ∀ᵐ g ∂μ, Matrix.of g ∈ UH (Hd k η) := hμ.2.2.1
    filter_upwards [this] with g hg h
    exact ⟨hg, ((abs_id hη hg).ge.trans h).trans_lt hs⟩
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ hρ
    have hρ' : ρ ^ 2 / 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
    have hA0 : Continuous fun X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) =>
        (Matrix.of.symm (NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _))) : PI.MtM k) :=
      GlobalTheory.GramExp.exp_cont.comp (unrealify_cont.comp continuous_subtype_val)
    have hA : MeasurableSet (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)) :=
      GlobalTheory.GramExp.measurableSet_image_ball hA0 _ _
    have hB : MeasurableSet ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) :=
      GlobalTheory.GramExp.measurableSet_image_ball (by fun_prop) _ _
    obtain ⟨τ, t1, t2, t3, t4⟩ := phase_law hη hμ hρ'
    rw [hvol ρ hρ.1, chart_image hη hexp hρ.1 hρ.2, prod_top hη hμ hμ₀ h1 hρ' hA hB, ← t1 _ hB,
      GlobalTheory.T.rotationInvariant_measure_unitCircle_arc τ ρ t2 t3 t4 hρ.1 (by linarith [hρ.2, Real.pi_gt_three]), t1 _ MeasurableSet.univ]
    simp

end GlobalTheory.Tube
