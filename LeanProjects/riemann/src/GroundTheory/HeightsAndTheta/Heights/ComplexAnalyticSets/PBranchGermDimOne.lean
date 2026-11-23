import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroDimIsolated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimComponentBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal

theorem VarBranch.dimH_image_le_two {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) : dimH c.image ≤ 2 := by
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hι : ∀ τ : ℂ, ‖ι τ‖ = ‖τ‖ := fun τ ↦ by simp [ι, pi_norm_const]
  have himg : c.image = (c.toFun ∘ ι) '' Metric.ball 0 c.radius := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t 0, ?_, ?_⟩
      · have h0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        linarith
      · simp only [Function.comp, ι]
        congr 1
        funext i
        rw [Subsingleton.elim i 0]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨ι τ, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
      rwa [hι]
  have hd : DifferentiableOn ℂ (c.toFun ∘ ι) (Metric.ball 0 c.radius) := by
    have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
    refine c.differentiableOn.comp hιd.differentiableOn fun τ hτ ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
    rwa [hι]
  have hcd : ContDiffOn ℝ 1 (c.toFun ∘ ι) (Metric.ball 0 c.radius) :=
    (hd.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ
  rw [himg]
  calc dimH ((c.toFun ∘ ι) '' Metric.ball 0 c.radius) ≤ dimH (Metric.ball (0 : ℂ) c.radius) :=
        hcd.dimH_image_le (convex_ball 0 c.radius) le_rfl
    _ ≤ dimH (Set.univ : Set ℂ) := dimH_mono (Set.subset_univ _)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]; norm_num

theorem BranchGermDimOne.proof (h₀ : LocalDimComponentBound.Statement) (h₁ : ZeroDimIsolated.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : BranchGermDimOne.Statement := by
  intro n I q m c hm ⟨N, hN, hcov⟩
  let c₀ := c ⟨0, hm⟩
  have hq : q ∈ zeroSet I := c₀.map_zero ▸ c₀.mapsTo (Metric.mem_ball_self c₀.radius_pos)
  have hdimH : dimH (zeroSet I ∩ N) ≤ 2 :=
    (dimH_mono hcov).trans ((dimH_iUnion _).le.trans (iSup_le fun b ↦ (c b).dimH_image_le_two))
  apply le_antisymm
  · obtain ⟨W, hW, hIW, hqW, hle⟩ := h₀ n I q hq
    have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) := by
      refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := by
      have := hW
      exact ringKrullDim_nonneg_of_nontrivial
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
      revert hnn hup
      generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = x
      intro hup hnn
      induction x using WithBot.recBotCoe with
      | bot => exact absurd hnn (by simp)
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
        | coe d => exact ⟨d, rfl⟩
    rw [hd] at hle
    refine hle.trans ?_
    by_contra hlt
    have h2 : 2 ≤ d := by
      by_contra h
      exact hlt (by exact_mod_cast (by omega : d ≤ 1))
    have hpos := h₂ n d W hW hd q (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) hqW
    have hsub : zeroSet W ∩ interior N ⊆ zeroSet I ∩ N :=
      fun x hx ↦ ⟨fun f hf ↦ hx.1 f (hIW hf), interior_subset hx.2⟩
    have hlt' : dimH (zeroSet W ∩ interior N) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      refine ((dimH_mono hsub).trans hdimH).trans_lt ?_
      rw [ENNReal.coe_natCast]
      exact_mod_cast (by omega : 2 < 2 * d)
    have h0 := hausdorffMeasure_of_dimH_lt hlt'
    rw [NNReal.coe_natCast] at h0
    exact hpos.ne' h0
  · by_contra hlt
    have h0 : ringKrullDim (curveLocalRing I q) ≤ 0 := by
      generalize ringKrullDim (curveLocalRing I q) = x at hlt
      induction x using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        have he : e < 1 := by
          by_contra h'
          exact hlt (by exact_mod_cast not_lt.1 h')
        rw [Order.lt_one_iff] at he
        subst he
        exact le_rfl
    obtain ⟨N', hN', hiso⟩ := h₁ n I q h0
    have hcont : ContinuousAt c₀.toFun 0 :=
      c₀.differentiableOn.continuousOn.continuousAt (Metric.ball_mem_nhds 0 c₀.radius_pos)
    have hN'' : N' ∈ 𝓝 (c₀.toFun 0) := by rw [c₀.map_zero]; exact hN'
    have hev : ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N' :=
      Filter.Eventually.and (Metric.ball_mem_nhds 0 c₀.radius_pos) (hcont hN'')
    have hne : (𝓝[≠] (0 : Fin 1 → ℂ)).NeBot := inferInstance
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : Fin 1 → ℂ), (t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N') ∧ t ≠ 0 :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and self_mem_nhdsWithin
    obtain ⟨t, ⟨ht, htN⟩, ht0⟩ := hev'.exists
    have hx : c₀.toFun t = q := hiso ⟨c₀.mapsTo ht, htN⟩
    exact ht0 (c₀.injOn ht (Metric.mem_ball_self c₀.radius_pos) (hx.trans c₀.map_zero.symm))

end GroundTheory.Heights₂.Heights
