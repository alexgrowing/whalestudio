import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FinIwa
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem ray_lv {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hf : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (Real.exp_neg t)
  rw [Subgroup.coe_mul, blkLaws.1, Subgroup.coe_one, one_mul, one_mul, zt, zt, h]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evInj :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ = 0 → φ = 0 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA r w ι₄ hw hι φ hφ h0
  obtain ⟨f, hf, hfa, ⟨U, -, hU⟩, rfl⟩ := ((zMem μ₂ τ₁ τ₂ κ e hA.idem).1 _ φ).1 hφ
  have h1 : ∀ g m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 (ι₄ g)) = 0 := fun g m₁ m₂ =>
    (mul_eq_zero.1 (congrFun (congrFun h0 g) (m₁, m₂))).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨ι₂, hι₂⟩ := (embEx (K := K) 2 w hw).1
  have hz : f = 0 := by
    refine hA.inj f hf hfa fun h m₁ m₂ => ?_
    obtain ⟨X, a₁, a₂, t, g, u, hu, hd⟩ := finIwa w ι₄ hw hι h k₀
    obtain ⟨X', hX⟩ := (parLaw w ι₂ ι₄ hw hι₂ hι).1 m₁ m₂ 0 X
    have hl : lv m₁ m₂ 0 * lv a₁ a₂ t = lv 1 1 t * lv (m₁ * a₁) (m₂ * a₂) 0 := by
      rw [blkLaws.2.1, blkLaws.2.1, one_mul, one_mul, zero_add, add_zero]
    have he : lv m₁ m₂ 0 * arc1 k₀ * fin1 h =
        nn X' * (lv 1 1 t * (lv (m₁ * a₁) (m₂ * a₂) 0 * arc1 k₀ * fin1 (ι₄ g))) * fin1 u := by
      rw [mul_assoc, hd]
      simp only [← mul_assoc]
      rw [hX, mul_assoc (nn X'), hl, ← mul_assoc (nn X')]
    rw [he, hU u (hu U), hf.unip, ray_lv hf, h1]
  funext x
  rw [hz]
  exact mul_zero _
