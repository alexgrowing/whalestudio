import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralUnipFundamentalDomainCompLatticePreservi

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GroundTheory.Automorphic.CuspidalProjection
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section

variable {K : Type} [Field K] [NumberField K]

private theorem unip_mem_iff {n r : ℕ} (Y : UPos n r → 𝔸[K]) :
    unipOne K n r Y ∈ Gam K n ↔ Y ∈ unipLattice K n r := by
  refine ⟨fun h => ?_, fun h => unipOne_mem_rationalGLOne r ⟨Y, h⟩⟩
  obtain ⟨g, hg⟩ : (unipGL Y : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.rationalGL K n := h
  refine ⟨fun p => (g : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2, funext fun p => ?_⟩
  have h1 := congrArg (fun x : AdelicGLn.AdelicGL K n => (x : Matrix (Fin n) (Fin n) 𝔸[K]) p.1.1 p.1.2) hg
  have hne : p.1.1 ≠ p.1.2 := fun e => by
    have := p.2
    rw [e] at this
    omega
  simp only [AdelicGLn.diagonal_apply, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2,
    Matrix.one_apply_ne hne, zero_add] at h1
  exact h1

private theorem ct_unip {n r : ℕ} {ψ : G1 K n → ℂ} (hψ : ∀ γ ∈ Gam K n, ∀ x, ψ (γ * x) = ψ x)
    (Y : UPos n r → 𝔸[K]) (z : G1 K n) : ct r ψ (unipOne K n r Y * z) = ct r ψ z := by
  unfold ct
  have h : ∀ X, unipOne K n r X * (unipOne K n r Y * z) = unipOne K n r (X + Y) * z := by
    intro X
    rw [unipOne_add, mul_assoc]
  simp_rw [h]
  refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
    (h := fun X => ψ (unipOne K n r X * z)) (fun ξ hξ s => ?_) Y
  show ψ (unipOne K n r (ξ + s) * z) = ψ (unipOne K n r s * z)
  rw [unipOne_add, mul_assoc, hψ _ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]

private theorem ct_levi {ψ : G1 K (2 + 2) → ℂ} (hψ : ∀ γ ∈ Gam K (2 + 2), ∀ x, ψ (γ * x) = ψ x)
    (γ₁ γ₂ : G1 K 2) (hl : lv γ₁ γ₂ 0 ∈ Gam K (2 + 2)) (z : G1 K (2 + 2)) :
    ct 2 ψ (lv γ₁ γ₂ 0 * z) = ct 2 ψ z := by
  obtain ⟨e, he, -⟩ := adMeas γ₁ γ₂ 0
  have hlat : ∀ X, e X ∈ unipLattice K (2 + 2) 2 ↔ X ∈ unipLattice K (2 + 2) 2 := by
    intro X
    rw [← unip_mem_iff, ← unip_mem_iff]
    have h : unipOne K (2 + 2) 2 (e X) = (lv γ₁ γ₂ 0)⁻¹ * unipOne K (2 + 2) 2 X * lv γ₁ γ₂ 0 := by
      rw [mul_assoc, he X, inv_mul_cancel_left]
    rw [h]
    constructor
    · intro h'
      have h2 := mul_mem (mul_mem hl h') (inv_mem hl)
      simpa [mul_assoc] using h2
    · exact fun h' => mul_mem (mul_mem (inv_mem hl) h') hl
  have key := UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (2 + 2) 2 e hlat (fun X => ψ (unipOne K (2 + 2) 2 X * z)) (fun ξ hξ X => by
    show ψ (unipOne K (2 + 2) 2 (ξ + X) * z) = ψ (unipOne K (2 + 2) 2 X * z)
    rw [unipOne_add, mul_assoc, hψ _ (unipOne_mem_rationalGLOne 2 ⟨ξ, hξ⟩)])
  unfold ct
  rw [← key]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  show ψ (unipOne K (2 + 2) 2 X * (lv γ₁ γ₂ 0 * z)) = ψ (unipOne K (2 + 2) 2 (e X) * z)
  rw [← mul_assoc, he X, mul_assoc, hψ _ hl]

private theorem kc_ex {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) (r : ℕ) :
    ∃ kc : G1 K n → L2 μ, Continuous kc ∧ ∀ φ z, ⟪kc z, φ⟫_ℂ = ct r (rc μ a φ) z := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hk := kvCont K n μ a
  have hj : Continuous fun p : (UPos n r → 𝔸[K]) × G1 K n => kv μ a (unipOne K n r p.1 * p.2) :=
    hk.comp (continuous_unipOne_mul r)
  have hint : ∀ z, IntegrableOn (fun X => kv μ a (unipOne K n r X * z)) (unipFundamentalDomain K n r)
      (unipMeasure K n r) := fun z =>
    ((hj.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact hC).mono_set hDC
  haveI : IsFiniteMeasure ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
  refine ⟨fun z => ∫ X in unipFundamentalDomain K n r, kv μ a (unipOne K n r X * z) ∂unipMeasure K n r, ?_,
    fun φ z => ?_⟩
  · haveI : SecondCountableTopology (G1 K n) := inferInstance
    haveI : FirstCountableTopology (G1 K n) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds z₀
    obtain ⟨M, hM⟩ := (hC.prod hVc).exists_bound_of_continuousOn hj.continuousOn
    refine continuousAt_of_dominated (bound := fun _ => M)
      (Eventually.of_forall fun z => (hint z).aestronglyMeasurable) ?_ (integrable_const M) ?_
    · filter_upwards [hV] with z hz
      exact (ae_restrict_iff' measurableSet_unipFundamentalDomain).2
        (Eventually.of_forall fun X hX => hM (X, z) ⟨hDC hX, hz⟩)
    · exact Eventually.of_forall fun X => (hk.comp (continuous_const_mul _)).continuousAt
  · show ⟪∫ X in unipFundamentalDomain K n r, kv μ a (unipOne K n r X * z) ∂unipMeasure K n r, φ⟫_ℂ =
      ∫ X in unipFundamentalDomain K n r, rc μ a φ (unipOne K n r X * z) ∂unipMeasure K n r
    rw [← inner_conj_symm, ← integral_inner (hint z) φ, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    show conj ⟪φ, kv μ a (unipOne K n r X * z)⟫_ℂ = _
    rw [inner_conj_symm, inner_kv]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctKv :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)), (∀ r, ∃ kc : G1 K (2 + 2) → L2 μ, Continuous kc ∧ ∀ φ z, ⟪kc z, φ⟫_ℂ = ct r (rc μ a φ) z) ∧
      ∀ φ : L2 μ, Continuous (rc μ a φ) ∧ Reps μ (Rop μ a φ) (rc μ a φ) ∧ (∀ γ ∈ Gam K (2 + 2), ∀ x, rc μ a φ (γ * x) = rc μ a φ x) ∧
        (∀ γ ∈ PK K, ∀ z, ct 2 (rc μ a φ) (γ * z) = ct 2 (rc μ a φ) z) ∧ ∀ X z, ct 2 (rc μ a φ) (nn X * z) = ct 2 (rc μ a φ) z := by
  intro K _ _ μ _ a
  refine ⟨fun r => kc_ex μ a r, fun φ => ?_⟩
  have hinv : ∀ γ ∈ Gam K (2 + 2), ∀ x, rc μ a φ (γ * x) = rc μ a φ x :=
    fun γ hγ x => rconv_mul_left (Gam K (2 + 2)) μ a φ hγ x
  refine ⟨continuous_rconv (Gam K (2 + 2)) μ a φ, ?_, hinv, fun γ hγ z => ?_, fun X z => ct_unip hinv X z⟩
  · have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
    filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae
      (integrated_ae_eq_rconvQ (Gam K (2 + 2)) μ a φ)] with y hy
    exact hy
  · obtain ⟨ξ, γ₁, γ₂, rfl⟩ := (pkLaws (K := K)).2.1 γ |>.1 hγ
    have hγG : nn ξ.1 * lv (γ₁ : G1 K 2) (γ₂ : G1 K 2) 0 ∈ Gam K (2 + 2) := by
      obtain ⟨g, -, hg⟩ := hγ
      rw [← hg]
      exact g.2
    have hl : lv (γ₁ : G1 K 2) (γ₂ : G1 K 2) 0 ∈ Gam K (2 + 2) := by
      have h2 := mul_mem (inv_mem (unipOne_mem_rationalGLOne 2 ξ)) hγG
      simpa using h2
    rw [mul_assoc, ct_unip hinv, ct_levi hinv _ _ hl]
