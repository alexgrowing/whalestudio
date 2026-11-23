import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.MainBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.LamRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmBdReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.HsOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

private theorem le_of_sq_le {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (h : t ^ 2 ≤ B * t) : t ≤ B := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncKer :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → IsLeftSmooth a → D.Hecke a →
      ∃ kk : ℝ → G1 K (2 + 2) → L2 μ, (∀ T, ∀ γ ∈ Gam K (2 + 2), ∀ x, kk T (γ * x) = kk T x) ∧ (∀ T x, Om T x → kk T x = P (kv μ a x)) ∧
        (∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T x, 0 ≤ T → ¬ Om T x → ‖kk T x‖ ≤ C * (qht x ^ N')⁻¹) ∧
        (∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ T x, 0 ≤ T → ‖kk T x‖ ≤ C * qht x ^ N) ∧
        ∀ T Λ, 0 ≤ T → IsTrunc A.J A'.J T Λ → (∃ B : ℝ, ∀ x, ‖kk T x‖ ≤ B) ∧
          StronglyMeasurable (fun y : RightCosetSpace (Gam K (2 + 2)) => kk T (Quotient.out y)) ∧ IsHilbertSchmidt (Λ ∘L Rop μ a ∘L P) ∧
          ∀ φ, ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) =ᵐ[quotientMeasure (Gam K (2 + 2)) μ] fun y => ⟪kk T (Quotient.out y), φ⟫_ℂ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha hD
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
  haveI hsf : SFinite (quotientMeasure (Gam K (2 + 2)) μ) := sfinite_of_finite _
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  haveI : MeasurableSpace.CountablyGenerated (RightCosetSpace (Gam K (2 + 2))) := BorelSpace.countablyGenerated
  haveI : IsSeparable (quotientMeasure (Gam K (2 + 2)) μ) := isSeparable_of_sigmaFinite _
  haveI : SecondCountableTopology (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) := Lp.SecondCountableTopology
  haveI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  choose k hk hkγ hkO hkm using fun T => UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kT μ a T
  have hsa : ∀ u w : L2 μ, ⟪P u, w⟫_ℂ = ⟪u, P w⟫_ℂ := fun u w => hP.1.isSymmetric u w
  have hPP : ∀ u : L2 μ, P (P u) = P u := fun u => DFunLike.congr_fun hP.2.1 u
  have hsq : ∀ u : L2 μ, ‖P u‖ ^ 2 = ‖⟪u, P u⟫_ℂ‖ := by
    intro u
    have h : ⟪u, P u⟫_ℂ = ⟪P u, P u⟫_ℂ := by rw [hsa, hPP]
    rw [h, inner_self_eq_norm_sq_to_K]
    simp
  have hPn : ∀ u : L2 μ, ‖P u‖ ≤ ‖u‖ := fun u =>
    le_of_sq_le (norm_nonneg _) (norm_nonneg _) ((hsq u).trans_le (norm_inner_le_norm _ _))
  obtain ⟨q1, -, -⟩ := qhtBasic K (2 + 2)
  have q0 : ∀ x : G1 K (2 + 2), 0 ≤ qht x := fun x => zero_le_one.trans (q1 x)
  have hfar : ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T x, 0 ≤ T → ¬ Om T x → ‖P (k T x)‖ ≤ C * (qht x ^ N')⁻¹ := by
    intro N'
    obtain ⟨C, hC, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.mainBd K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha hD N'
    refine ⟨C, hC, fun T x hT hx => ?_⟩
    refine le_of_sq_le (norm_nonneg _) (mul_nonneg hC (inv_nonneg.2 (pow_nonneg (q0 x) _))) ?_
    rw [hsq, hk]
    exact h T x _ hT (hPP _) hx
  obtain ⟨C₁, N₁, hC₁, b₁⟩ := (kvBd K (2 + 2) μ a).1 (UpperTheory.ConvolutionTheory.C.polyBdAll K (2 + 2) μ a)
  obtain ⟨C₂, hC₂, b₂⟩ := hfar 0
  have hnear : ∀ T x, Om T x → ‖P (k T x)‖ ≤ C₁ * qht x ^ N₁ := fun T x hx => by
    rw [hkO T x hx]; exact (hPn _).trans (b₁ x)
  have hfar0 : ∀ T x, 0 ≤ T → ¬ Om T x → ‖P (k T x)‖ ≤ C₂ := fun T x hT hx => by simpa using b₂ T x hT hx
  refine ⟨fun T x => P (k T x), fun T γ hγ x => by simp only [hkγ T γ hγ x], fun T x hx => by simp only [hkO T x hx], hfar,
    ⟨C₁ + C₂, N₁, add_nonneg hC₁ hC₂, fun T x hT => ?_⟩, fun T Λ hT hΛ => ?_⟩
  · have h1 : 1 ≤ qht x ^ N₁ := one_le_pow₀ (q1 x)
    by_cases hx : Om T x
    · exact (hnear T x hx).trans (by nlinarith)
    · exact (hfar0 T x hT hx).trans (by nlinarith)
  · obtain ⟨C, c, N, -, hC, hb⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd (K := K)
    have hB : ∀ x, ‖P (k T x)‖ ≤ C₁ * (C * Real.exp (N * T)) ^ N₁ + C₂ := by
      intro x
      by_cases hx : Om T x
      · refine (hnear T x hx).trans (le_add_of_le_of_nonneg ?_ hC₂)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 x) ((hb T x hT).1 hx) _) hC₁
      · exact (hfar0 T x hT hx).trans (le_add_of_nonneg_left (by positivity))
    have hm : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => P (k T (Quotient.out y)) :=
      P.continuous.comp_stronglyMeasurable (hkm T)
    have hae : ∀ φ, ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) =ᵐ[quotientMeasure (Gam K (2 + 2)) μ]
        fun y => ⟪P (k T (Quotient.out y)), φ⟫_ℂ := by
      intro φ
      have hr := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lamRep K μ μ₂ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ).2.2 a hD (P φ) (hPP φ)
      have hm2 : ∀ᵐ y ∂(Measure.map (mk (Gam K (2 + 2))) (μ.restrict (fundamentalDomain (Gam K (2 + 2))))),
          ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) y = ⟪P (k T (Quotient.out y)), φ⟫_ℂ := by
        refine (ae_map_iff (measurable_mk (Gam K (2 + 2))).aemeasurable
          (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
            (hm.inner stronglyMeasurable_const).measurable)).2 ?_
        refine ae_restrict_of_ae (Filter.Eventually.mono hr fun y hy => ?_)
        obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1
          (show mk (Gam K (2 + 2)) (Quotient.out (mk (Gam K (2 + 2)) y)) = mk (Gam K (2 + 2)) y from Quotient.out_eq _)
        have e : k T (Quotient.out (mk (Gam K (2 + 2)) y)) = k T y := by
          rw [← hγ]; exact hkγ T _ γ.2 y
        rw [e, hsa, hk]
        exact hy
      rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K (2 + 2)) μ)] at hm2
    exact ⟨⟨_, hB⟩, hm, hsOfKer (quotientMeasure (Gam K (2 + 2)) μ) _ _ (MemLp.of_bound hm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun y => hB _)) hae, hae⟩
