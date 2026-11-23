import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff Pointwise

namespace GlobalTheory.RadVol

private theorem measure_slice_le_measure_mul_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] {N : Set G} {ν : Measure G} (hnull : ν Nᶜ = 0)
    (hleft : ∀ m ∈ N, Measure.map (fun x => m * x) ν = ν) {K S : Set G} (hK : IsCompact K) (g : G) :
    ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν (K * K⁻¹) := by
  by_cases h0 : ∃ s₀ ∈ N, s₀⁻¹ * g ∈ K
  · obtain ⟨s₀, hs₀, hk₀⟩ := h0
    have hKK : MeasurableSet (K * K⁻¹) := (hK.mul hK.inv).isClosed.measurableSet
    have hpre : MeasurableSet ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := hKK.preimage (measurable_const_mul _)
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          apply measure_mono
          intro s hs
          simp only [Set.mem_preimage]
          rw [show s₀⁻¹ * s = (s₀⁻¹ * g) * (s⁻¹ * g)⁻¹ by group]
          exact Set.mul_mem_mul hk₀ (Set.inv_mem_inv.mpr hs.2)
      _ = Measure.map (fun x => s₀ * x) ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          rw [hleft s₀ hs₀]
      _ = ν ((fun x => s₀ * x) ⁻¹' ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹))) :=
          Measure.map_apply (measurable_const_mul _) hpre
      _ = ν (K * K⁻¹) := by
          congr 1
          ext x
          simp
  · push_neg at h0
    have hsub : {s | s ∈ S ∧ s⁻¹ * g ∈ K} ⊆ Nᶜ := fun s hs hsN => h0 s hsN hs.2
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν Nᶜ := measure_mono hsub
      _ = 0 := hnull
      _ ≤ ν (K * K⁻¹) := bot_le

theorem measure_mul_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {N : Set G} {ν : Measure G} (hν : IsHaarSub N ν) {K S T : Set G} (hK : IsCompact K) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ T) : ν S * μ K ≤ ν (K * K⁻¹) * μ T := by
  classical
  obtain ⟨-, hfc, hnull, hleft⟩ := hν
  haveI : IsFiniteMeasureOnCompacts ν := hfc
  haveI : SigmaFinite ν := inferInstance
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set E : Set (G × G) := {p | p.1 ∈ S ∧ p.1⁻¹ * p.2 ∈ K} with hEd
  have hE : MeasurableSet E :=
    (measurable_fst hS).inter ((measurable_fst.inv.mul measurable_snd) hKm)

  have h1 : ν.prod μ E = ν S * μ K := by
    rw [Measure.prod_apply hE]
    have hsl : ∀ s, μ (Prod.mk s ⁻¹' E) = S.indicator (fun _ => μ K) s := by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_apply, if_pos hs, ← measure_preimage_mul μ s⁻¹ K]
        congr 1
        ext x
        simp [hEd, hs]
      · rw [Set.indicator_apply, if_neg hs]
        have h0 : Prod.mk s ⁻¹' E = ∅ := by
          ext x
          simp [hEd, hs]
        rw [h0, measure_empty]
    simp_rw [hsl]
    rw [lintegral_indicator_const hS, mul_comm]

  have h2 : ν.prod μ E ≤ ν (K * K⁻¹) * μ T := by
    rw [Measure.prod_apply_symm hE]
    calc ∫⁻ g, ν ((fun s => (s, g)) ⁻¹' E) ∂μ
        ≤ ∫⁻ g, T.indicator (fun _ => ν (K * K⁻¹)) g ∂μ := by
          apply lintegral_mono
          intro g
          by_cases hg : g ∈ T
          · rw [Set.indicator_apply, if_pos hg]
            exact (le_of_eq (by rw [hEd]; rfl)).trans
              (measure_slice_le_measure_mul_inv (S := S) hnull hleft hK g)
          · rw [Set.indicator_apply, if_neg hg]
            have h0 : (fun s => (s, g)) ⁻¹' E = ∅ := by
              ext s
              simp only [hEd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and]
              intro hs hk
              apply hg
              simpa using h s hs _ hk
            exact le_of_eq (by show ν ((fun s => (s, g)) ⁻¹' E) = 0; rw [h0, measure_empty])
      _ = ν (K * K⁻¹) * μ T := lintegral_indicator_const hT _
  calc ν S * μ K = ν.prod μ E := h1.symm
    _ ≤ ν (K * K⁻¹) * μ T := h2

private theorem dOp_nonneg_subadditive_continuous {n : ℕ} (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧
      (∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g')) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = 0 := by
      intro g
      have hz : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ = 0 := by
        refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
        rw [zero_mul, EuclideanSpace.norm_eq]
        simp
      simp only [dOp, hz, Real.log_zero]
    simp only [h0]
    exact ⟨fun _ => le_rfl, fun _ _ => by norm_num, continuous_const⟩
  · obtain ⟨-, h2, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g g' => (h2 g g' hn).2.2.1, h5⟩

theorem radical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)),
    IsIsoC ε W → IsHaarSub (NW ε W) ν →
    (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧
    ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  intro n ε W ν _ hν
  obtain ⟨hP, hM, hD⟩ := dOp_nonneg_subadditive_continuous ε
  haveI : (muG ε).IsHaarMeasure := by
    first
    | infer_instance
    | (unfold muG; infer_instance)
  have hgrowth : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
    obtain ⟨C, -, hball⟩ := GlobalTheory.BallVol.ballVol n ε
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : UJ ε)
    have hμK : 0 < muG ε K := by
      first
      | exact measure_pos_of_mem_nhds (μ := muG ε) hK1
      | exact (muG ε).measure_pos_of_mem_nhds hK1
      | exact Measure.measure_pos_of_mem_nhds (muG ε) hK1
    have hμKt : muG ε K < ⊤ := by
      first
      | exact hKc.measure_lt_top (μ := muG ε)
      | exact IsCompact.measure_lt_top hKc
    have hνKK : ν (K * K⁻¹) < ⊤ := by
      haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
      exact (hKc.mul hKc.inv).measure_lt_top
    obtain ⟨B, hB⟩ := hKc.bddAbove_image hD.continuousOn
    refine ⟨(ν (K * K⁻¹)).toReal * C * Real.exp (4 * n * rkR ε * max B 0) / (muG ε K).toReal,
      fun r hr => ?_⟩

    have hmul : ∀ s ∈ {m : UJ ε | dOp (umat m) ≤ r}, ∀ k ∈ K,
        s * k ∈ {m : UJ ε | dOp (umat m) ≤ r + max B 0} := by
      intro s hs k hk
      have hkB : dOp (umat k) ≤ B := hB (Set.mem_image_of_mem _ hk)
      have hs' : dOp (umat s) ≤ r := hs
      show dOp (umat (s * k)) ≤ r + max B 0
      linarith [hM s k, le_max_left B 0]
    have key := measure_mul_le (muG ε) hν (S := {m : UJ ε | dOp (umat m) ≤ r})
      (T := {m : UJ ε | dOp (umat m) ≤ r + max B 0}) hKc (measurableSet_le hD.measurable measurable_const)
      (measurableSet_le hD.measurable measurable_const) hmul
    have hT : muG ε {m : UJ ε | dOp (umat m) ≤ r + max B 0} ≤
        ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * (r + max B 0))) :=
      hball _ (add_nonneg hr (le_max_right B 0))
    have hm : 0 < (muG ε K).toReal := ENNReal.toReal_pos hμK.ne' hμKt.ne
    have key2 : ν {m : UJ ε | dOp (umat m) ≤ r} * ENNReal.ofReal (muG ε K).toReal ≤
        ENNReal.ofReal ((ν (K * K⁻¹)).toReal * (C * Real.exp (4 * n * rkR ε * (r + max B 0)))) := by
      rw [ENNReal.ofReal_toReal hμKt.ne, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hνKK.ne]
      exact key.trans (by gcongr)
    have key3 := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hm).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr key2
    rw [← ENNReal.ofReal_div_of_pos hm] at key3
    refine key3.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [mul_add, Real.exp_add]
    ring
  refine ⟨hgrowth, fun b hb => ?_⟩
  obtain ⟨C, hC⟩ := hgrowth
  exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) ν (fun m => dOp (umat m)) (4 * n * rkR ε) b C
    hD.measurable hP hC hb

end GlobalTheory.RadVol
