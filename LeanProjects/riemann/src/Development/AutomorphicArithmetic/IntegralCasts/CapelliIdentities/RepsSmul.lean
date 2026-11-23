import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AeFundamentalDomain

open MeasureTheory GroundTheory.Automorphic

private theorem UpperTheory.Reformulated.B.Glb3.ae_pull {G : Type} [Group G] (Γ : Subgroup G) [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [DiscreteTopology ↥Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (p : RightCosetSpace Γ → Prop)
    (hp : ∀ᵐ q ∂(RightCosetSpace.quotientMeasure Γ μ), p q) :
    ∀ᵐ y ∂μ, p (RightCosetSpace.mk Γ y) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine UpperTheory.ae_fundamental_domain Γ μ (RightCosetSpace.fundamentalDomain Γ) (RightCosetSpace.mk Γ)
    measurable_quotient_mk'' (fun γ g => Quotient.sound ⟨γ, rfl⟩) (fun g => ?_) p hp
  unfold RightCosetSpace.fundamentalDomain
  generalize_proofs h
  exact (h.choose_spec.2 g).exists

private theorem UpperTheory.Reformulated.B.Glb3.reps_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (μ : Measure (PositivityTheory.Rg.Tf.Core.G1 K n)) [μ.IsHaarMeasure] (v : PositivityTheory.Rg.Tf.Core.L2 μ)
    (φ : PositivityTheory.Rg.Tf.Core.G1 K n → ℂ) (c : ℂ) (h : PositivityTheory.Rg.Tf.Adel.Reps μ v φ) :
    PositivityTheory.Rg.Tf.Adel.Reps μ (c • v) (c • φ) := by
  have h1 := UpperTheory.Reformulated.B.Glb3.ae_pull (PositivityTheory.Rg.Tf.Core.Gam K n) μ _ (Lp.coeFn_smul c v)
  filter_upwards [h, h1] with y hy hy1
  exact hy1.trans (congrArg (c • ·) hy)

theorem UpperTheory.Reformulated.B.Glb3.sec_add :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {μ₂ : MeasureTheory.Measure (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ))}
      [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (PositivityTheory.Rg.Tf.Core.L2 μ₂)}
      {f f' : PositivityTheory.Rg.Tf.Core.G1 K ((2 : ℕ) + (2 : ℕ)) → ℂ},
      PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f →
        PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f' → ∀ (c : ℂ), PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ (f + c • f') := by
  intro K _ _ μ _ τ₁ τ₂ f f' hf hf' c
  obtain ⟨h1, ⟨C, h2⟩, h3, h4, h5⟩ := hf
  obtain ⟨h1', ⟨C', h2'⟩, h3', h4', h5'⟩ := hf'
  refine ⟨h1.add (h1'.const_smul c), ⟨C + ‖c‖ * C', fun g => ?_⟩, fun X g => ?_,
    fun r x g hx => ?_, fun g => ?_⟩
  · refine (norm_add_le (f g) (c • f' g)).trans (add_le_add (h2 g) ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h2' g) (norm_nonneg c)
  · simp only [Pi.add_apply, Pi.smul_apply, h3 X g, h3' X g]
  · simp only [Pi.add_apply, Pi.smul_apply, h4 r x g hx, h4' r x g hx]
  · obtain ⟨d, φ, ψ, hφ, hψ, hs⟩ := h5 g
    obtain ⟨d', φ', ψ', hφ', hψ', hs'⟩ := h5' g
    refine ⟨d + d', Fin.append φ (fun i => c • φ' i), Fin.append ψ ψ', fun i => ?_, fun i => ?_,
      fun m₁ m₂ x hx => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hφ j
      · rw [Fin.append_right]
        obtain ⟨hc, v, hv, hr⟩ := hφ' j
        exact ⟨hc.const_smul c, c • v, τ₁.smul_mem c hv, UpperTheory.Reformulated.B.Glb3.reps_smul μ v _ c hr⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hψ j
      · rw [Fin.append_right]; exact hψ' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hs m₁ m₂ x hx, hs' m₁ m₂ x hx, Finset.mul_sum, mul_assoc]
