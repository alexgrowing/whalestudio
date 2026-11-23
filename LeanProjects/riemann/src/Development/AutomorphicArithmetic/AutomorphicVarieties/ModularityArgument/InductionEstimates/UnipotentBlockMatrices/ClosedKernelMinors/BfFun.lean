import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bfFun :
    ∀ {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (β : ℝ → ℂ), SFun f → Continuous β → HasCompactSupport β → PFun (bf β f) ∧ InBand (bf β f) ∧ Decays (bf β f) := by
  intro K _ _ f β hf hβ hc
  obtain ⟨h1, -, h3, h4, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, hl, -⟩ := blkLaws (K := K)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun t => β t * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * t : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbf : ∀ g, bf β f g = w (HH g) * f g := fun g => by rw [hw]; rfl
  have hwc : Continuous w := by
    rw [hw]
    exact hβ.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hws : HasCompactSupport w := by
    rw [hw]
    exact hc.mul_right
  obtain ⟨B, hB⟩ := hwc.bounded_above_of_compact_support hws
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hn : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (g : G1 K (2 + 2)), HH (nn X * g) = HH g := fun X g => by
    have := h1 X 1 1 0 g
    rwa [hl, mul_one, zero_add] at this
  have hm : ∀ (m₁ m₂ : G1 K 2) (g : G1 K (2 + 2)), HH (lv m₁ m₂ 0 * g) = HH g := fun m₁ m₂ g => by
    have := h1 0 m₁ m₂ 0 g
    rwa [mul_assoc, hn, zero_add] at this
  have hle : ∀ g, ‖bf β f g‖ ≤ B * ‖f g‖ := fun g => by
    rw [hbf, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [show bf β f = fun g => w (HH g) * f g from funext hbf]
    exact (hwc.comp h4).mul hf.cont
  · obtain ⟨C, hC⟩ := hf.bdd
    exact ⟨B * C, fun g => (hle g).trans (mul_le_mul_of_nonneg_left (hC g) hB0)⟩
  · intro X g
    rw [hbf, hbf, hn, hf.unip]
  · intro γ hγ g
    rw [hbf, hbf, h3 γ hγ, hf.rat γ hγ]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₁ g, mul_zero]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₂ g, mul_zero]
  · obtain ⟨R, hR⟩ := hws.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun g hg => ?_⟩
    rw [hbf] at hg
    exact hR _ (subset_tsupport w (left_ne_zero_of_mul hg))
  · intro N R
    obtain ⟨C, hC⟩ := hf.dec N R
    refine ⟨B * C, fun x hx => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hC x hx
    refine ⟨γ, hγ, ?_⟩
    refine (mul_le_mul_of_nonneg_right (hle x) (pow_nonneg (AutomorphicForm.height_pos _).le N)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h hB0
