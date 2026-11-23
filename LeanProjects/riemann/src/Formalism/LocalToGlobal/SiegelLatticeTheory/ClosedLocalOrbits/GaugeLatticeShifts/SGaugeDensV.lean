import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem continuous_expC (ε : Fin n → Bool) : Continuous (expC ε) :=
  (continuous_expG ε).comp (obG ε).repr.symm.continuous

theorem expC_injOn (ε : Fin n → Bool) : ∃ ρ₀ > 0, Set.InjOn (expC ε) (Metric.ball 0 ρ₀) := by
  obtain ⟨ρ₀, hρ, hinj⟩ := injOn_thetaExp ε
  refine ⟨ρ₀, hρ, fun a ha b hb e => hinj ha hb ?_⟩
  have e2 := congrArg uMat e
  rw [uMat_expC, uMat_expC] at e2
  exact Matrix.of.injective e2

theorem lamM_apply (ε : Fin n → Bool) (s : ℝ) {B : Set (Formalism.REAL.UJ ε)} (hB : MeasurableSet B) :
    lamM ε s B = ∫⁻ t in expC ε ⁻¹' B ∩ Metric.ball 0 s, jd ε t := by
  have hm : MeasurableSet (expC ε ⁻¹' B) := (continuous_expC ε).measurable hB
  rw [lamM, Measure.map_apply (continuous_expC ε).measurable hB, withDensity_apply _ hm,
    Measure.restrict_restrict hm]

theorem locInvOf (ε : Fin n → Bool) : LocInvOf ε := by
  intro hT hJ
  obtain ⟨s₁, hs₁, hTs⟩ := hT
  obtain ⟨ρ₀, hρ₀, hinj⟩ := expC_injOn ε
  refine ⟨min s₁ ρ₀, lt_min hs₁ hρ₀, fun s hs hss z A hA hAs hzA => ?_⟩
  have hinjs : Set.InjOn (expC ε) (Metric.ball 0 s) :=
    hinj.mono (Metric.ball_subset_ball (hss.trans (min_le_right _ _)))
  obtain ⟨U, hU, φ, hφ, hΘ, hsub⟩ := hTs s hs (hss.trans (min_le_left _ _)) z
  have hexp : ∀ t ∈ U, expC ε (φ t) = z * expC ε t := by
    intro t ht
    apply uMat_inj
    show _ = uMat z * uMat (expC ε t)
    simp only [uMat_expC]
    exact hΘ t ht
  set T := expC ε ⁻¹' A ∩ Metric.ball 0 s with hTdef
  have hTU : ∀ t ∈ T, t ∈ U ∧ φ t ∈ Metric.ball (0 : EL ε) s := fun t ht =>
    hsub t ht.2 (hzA ⟨expC ε t, ht.1, rfl⟩)
  have himage : φ '' T = expC ε ⁻¹' ((fun g => z * g) '' A) ∩ Metric.ball 0 s := by
    ext t'
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, (hTU t ht).2⟩
      show expC ε (φ t) ∈ (fun g => z * g) '' A
      rw [hexp t (hTU t ht).1]
      exact ⟨expC ε t, ht.1, rfl⟩
    · rintro ⟨⟨a, ha, hza⟩, ht'⟩
      obtain ⟨t, htb, rfl⟩ := hAs ha
      have htT : t ∈ T := ⟨ha, htb⟩
      refine ⟨t, htT, hinjs (hTU t htT).2 ht' ?_⟩
      rw [hexp t (hTU t htT).1]
      exact hza
  have hinjT : Set.InjOn φ T := by
    intro a ha b hb e
    apply hinjs ha.2 hb.2
    have e2 := congrArg (expC ε) e
    rw [hexp a (hTU a ha).1, hexp b (hTU b hb).1] at e2
    exact mul_left_cancel e2
  have hzAm : MeasurableSet ((fun g => z * g) '' A) := by
    have : (fun g => z * g) '' A = (fun g => z⁻¹ * g) ⁻¹' A := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
      · intro hg
        exact ⟨z⁻¹ * g, hg, by simp⟩
    rw [this]
    exact (continuous_const_mul z⁻¹).measurable hA
  have hTm : MeasurableSet T := ((continuous_expC ε).measurable hA).inter measurableSet_ball
  rw [lamM_apply ε s hzAm, lamM_apply ε s hA, ← himage,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hTm
      (fun t ht => ((hφ.differentiableAt (hU.mem_nhds (hTU t ht).1)).hasFDerivAt).hasFDerivWithinAt) hinjT]
  refine setLIntegral_congr_fun hTm (fun t ht => ?_)
  simp only [jd]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm, hJ U φ (uMat z) hU hφ hΘ t (hTU t ht).1]

end Formalism.MainNotions.S.Gauge
