import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem om_of_mul {K : Type} [Field K] [NumberField K] {T : ℝ} {γ : G1 K (2 + 2)} (hγ : γ ∈ Gam K (2 + 2))
    {x : G1 K (2 + 2)} (h : Om T x) : Om T (γ * x) := by
  intro q
  obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 (q.out * ⟨γ, hγ⟩)
  have h1 := h (Quotient.mk _ (q.out * ⟨γ, hγ⟩))
  unfold qx at h1 ⊢
  rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ, Subgroup.coe_mul, mul_assoc] at h1
  exact h1

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omMeas :
    ∀ {K : Type} [Field K] [NumberField K] (T : ℝ), (∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x) ∧ IsClosed {x : G1 K (2 + 2) | Om T x} ∧
      MeasurableSet {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} := by
  intro K _ _ T
  have h1 : ∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x := fun γ hγ x =>
    ⟨fun h => by
      have := om_of_mul (inv_mem hγ) h
      rwa [inv_mul_cancel_left] at this, om_of_mul hγ⟩
  have h2 : IsClosed {x : G1 K (2 + 2) | Om T x} := by
    unfold Om
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_le
      ((hpSpec (K := K)).2.2.2.1.comp (continuous_const.mul continuous_id)) continuous_const
  refine ⟨h1, h2, ?_⟩
  rw [measurableSet_quotient]
  have h : Quotient.mk'' ⁻¹' {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} =
      {x : G1 K (2 + 2) | Om T x} := by
    ext x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) x))
    change Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) x)) ↔ Om T x
    rw [← hγ]
    exact h1 _ γ.2 x
  rw [h]
  exact h2.measurableSet
