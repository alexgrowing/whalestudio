import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tower_point {G : Type*} [Group G] (Γ : Subgroup G) (P : Subgroup Γ) (E : Set G)
    (hE : ∀ x : G, ∃! γ : P.map Γ.subtype, γ • x ∈ E) (Ψ : G → ℝ≥0∞)
    (hΨ : ∀ γ ∈ P.map Γ.subtype, ∀ g, Ψ (γ * g) = Ψ g) (y : G) :
    ∑' γ : Γ, E.indicator Ψ ((γ : G) * y) =
      ∑' q : Quotient (QuotientGroup.rightRel P), Ψ (((q.out : Γ) : G) * y) := by
  classical
  rw [← (Equiv.sigmaFiberEquiv (fun γ : Γ => (Quotient.mk (QuotientGroup.rightRel P) γ))).tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun q => ?_
  obtain ⟨⟨δ, hδ⟩, hδE, huniq⟩ := hE (((q.out : Γ) : G) * y)
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hδ
  have hmk : Quotient.mk (QuotientGroup.rightRel P) (p * q.out) = q := by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Quotient.sound ?_
    change (QuotientGroup.rightRel P) _ _
    rw [QuotientGroup.rightRel_apply]
    simpa using P.inv_mem hp
  have hδE' : (p : G) * (((q.out : Γ) : G) * y) ∈ E := hδE
  rw [tsum_eq_single ⟨p * q.out, hmk⟩]
  · simp only [Equiv.sigmaFiberEquiv_apply, Subgroup.coe_mul, mul_assoc]
    rw [indicator_of_mem hδE']
    exact hΨ _ hδ _
  · rintro ⟨γ, hγ⟩ hne
    simp only [Equiv.sigmaFiberEquiv_apply]
    refine indicator_of_notMem (fun hmem => hne ?_) _
    have hrel : (QuotientGroup.rightRel P) q.out γ := by
      refine Quotient.exact ?_
      rw [Quotient.out_eq, hγ]
    rw [QuotientGroup.rightRel_apply] at hrel
    have h1 := huniq ⟨((γ * q.out⁻¹ : Γ) : G), Subgroup.mem_map.2 ⟨_, hrel, rfl⟩⟩ (by
      change ((γ * q.out⁻¹ : Γ) : G) * (((q.out : Γ) : G) * y) ∈ E
      simpa [mul_assoc] using hmem)
    have h2 : γ * q.out⁻¹ = p := Subtype.ext (congrArg (fun z : P.map Γ.subtype => (z : G)) h1)
    refine Subtype.ext ?_
    change γ = p * q.out
    rw [← h2]; simp

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tower :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (E : Set (G1 K (2 + 2))), MeasurableSet E → (∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E) →
      ∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
        ∫⁻ y, ∑' q : Cos K, Ψ ((q.out : G1 K (2 + 2)) * y) ∂fd μ = ∫⁻ g in E, Ψ g ∂μ := by
  intro K _ _ μ _ E hEm hE Ψ hΨm hΨ
  haveI : Countable (Gam K (2 + 2)) := inferInstance
  have hD := isFundamentalDomain_fundamentalDomain (Gam K (2 + 2)) μ
  rw [← lintegral_indicator hEm, hD.lintegral_eq_tsum'', ← lintegral_tsum]
  · refine lintegral_congr fun y => ?_
    exact (tower_point (Gam K (2 + 2)) (ParΓ K 2 2) E hE Ψ hΨ y).symm
  · intro γ
    exact ((hΨm.indicator hEm).comp (measurable_const_mul (γ : G1 K (2 + 2)))).aemeasurable
