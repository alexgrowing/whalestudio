import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ContLv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem bumpEx : ∃ β : ℝ → ℂ, Continuous β ∧ HasCompactSupport β ∧ (∫ t, conj (β t) * β t) ≠ 0 := by
  obtain ⟨b⟩ : Nonempty (ContDiffBump (0 : ℝ)) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  have hs : HasCompactSupport (fun t : ℝ => (b t) ^ 2) :=
    b.hasCompactSupport.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have h0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  refine ⟨fun t => ((b t : ℝ) : ℂ), Complex.continuous_ofReal.comp b.continuous,
    b.hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero, ?_⟩
  have h1 : ∀ t : ℝ, conj ((b t : ℝ) : ℂ) * ((b t : ℝ) : ℂ) = (((b t) ^ 2 : ℝ) : ℂ) := fun t => by
    rw [Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [h1]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun t : ℝ => (b t) ^ 2) (b.continuous.pow 2) hs (fun t => sq_nonneg _) (x := 0) ?_)
  rw [h0]
  norm_num

private theorem cancelN {N a p c : ℂ} (hN : N ≠ 0) (h : N * a = c * ((1 * N) * p)) : c * p = a := by
  have h2 : N * (a - c * p) = 0 := by
    rw [mul_sub, h]
    ring
  exact (sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hN)).symm

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secIp :
    ForAllC fun K _ _ μ _ μ₂ _ _ _ _ _ _ A A' => ∀ (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ), Unf μ μ₂ κ c →
      (∀ v w, c * ∫ k : KG K (2 + 2), pm μ₂ (A.sec v) (A.sec w) k k ∂κ = ⟪v, w⟫_ℂ) ∧ ∀ v w, ∫ k : KG K (2 + 2), pm μ₂ (A.sec v) (A'.sec w) k k ∂κ = 0 := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' κ _ c hU
  have hS : ∀ v, SFun (A.sec v) ∧ Slices τ₁ τ₂ (A.sec v) := fun v => by
    obtain ⟨hs, hx⟩ := (A.onto (A.sec v)).1 ⟨v, rfl⟩
    exact ⟨secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ hs hx,
      ((secCrit μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ hx).1 hs).2.2.2.2⟩
  have hS' : ∀ w, SFun (A'.sec w) ∧ Slices τ₂ τ₁ (A'.sec w) := fun w => by
    obtain ⟨hs, hx⟩ := (A'.onto (A'.sec w)).1 ⟨w, rfl⟩
    exact ⟨secFun μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ hs hx,
      ((secCrit μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ hx).1 hs).2.2.2.2⟩
  have hlaw := (pmLaws μ₂ κ).1
  refine ⟨fun v w => ?_, fun v w => ?_⟩
  · obtain ⟨β, hβc, hβs, hN⟩ := bumpEx
    obtain ⟨u, hu⟩ := (denseCc d).2.1 β v hβc hβs
    obtain ⟨u', hu'⟩ := (denseCc d).2.1 β w hβc hβs
    have hP := pairF μ μ₂ κ c hU _ _ β β (hS v).1 (hS w).1 hβc hβs hβc hβs _ _
      (A.spec β v u hβc hβs hu) (A.spec β w u' hβc hβs hu')
    have hw : ∀ x y, pw μ₂ (A.sec v) (A.sec w) x y = 0 := fun x y =>
      (hlaw τ₁ τ₂ τ₁ τ₂ _ _ (hS v).1 (hS w).1 (hS v).2 (hS w).2 x y).2 hp.orth
    simp only [hw, mul_zero, integral_zero, add_zero] at hP
    rw [A.J.inner_map_map, L2.inner_def] at hP
    have hin : ∫ x, ⟪u x, u' x⟫_ℂ = (∫ t, conj (β t) * β t) * ⟪v, w⟫_ℂ := by
      rw [← integral_mul_const]
      refine integral_congr_ae ?_
      filter_upwards [hu, hu'] with x h h'
      rw [h, h', inner_smul_left, inner_smul_right, mul_assoc]
    have hvol : volN K = 1 := (volOne (K := K) 0 0).2.1
    rw [hin, hvol] at hP
    rw [Complex.ofReal_one] at hP
    exact cancelN hN hP
  · have hz : ∀ x y, pm μ₂ (A.sec v) (A'.sec w) x y = 0 := fun x y =>
      (hlaw τ₁ τ₂ τ₂ τ₁ _ _ (hS v).1 (hS' w).1 (hS v).2 (hS' w).2 x y).1 hp.orth
    simp only [hz, integral_zero]
