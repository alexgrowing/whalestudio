import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ParHaar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.iwaInt :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧ ∀ Φ : G1 K (2 + 2) → ℝ≥0∞, Measurable Φ →
      ∫⁻ g, Φ g ∂μ = ENNReal.ofReal c * ∫⁻ m₁, ∫⁻ m₂, ∫⁻ t : ℝ, ∫⁻ k : KG K (2 + 2), ∫⁻ X,
        Φ (nn X * lv m₁ m₂ t * k) * ENNReal.ofReal (Real.exp (-4 * t)) ∂unipMeasure K (2 + 2) 2 ∂κ ∂volume ∂μ₂ ∂μ₂ := by
  intro K _ _ μ _ μ₂ _ κ _
  obtain ⟨S, ν, hS, hν, hmem, hΦ⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.parHaar (K := K) μ₂
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  have : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp hK
  have : μ.IsMulRightInvariant := isMulRightInvariant_normOneGL μ
  have hSK : Function.Surjective (HaarSK.mulMap S (KG K (2 + 2))) := by
    intro g
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.iwa (K := K) g
    exact ⟨(⟨_, (hmem _).2 ⟨X, m₁, m₂, t, rfl⟩⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c, hc0, hc⟩ := HaarSK.exists_lintegral_eq μ hS hK hSK ν κ
  refine ⟨c, by exact_mod_cast pos_iff_ne_zero.mpr hc0, fun Φ hm => ?_⟩
  have hφ : Measurable fun g : G1 K (2 + 2) => ∫⁻ k : KG K (2 + 2), Φ (g * k) ∂κ :=
    (hm.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'
  rw [hc Φ hm, hΦ _ hφ, ENNReal.ofReal_coe_nnreal]
  congr 1
  refine lintegral_congr fun m₁ => lintegral_congr fun m₂ => lintegral_congr fun t => ?_
  have hn : Measurable fun X : UPos (2 + 2) 2 → 𝔸[K] => nn X * lv m₁ m₂ t :=
    ((continuous_unipOne (K := K) (n := 2 + 2) 2).mul continuous_const).measurable
  rw [← lintegral_lintegral_swap]
  · refine lintegral_congr fun X => ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  · exact ((hm.comp ((hn.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))).mul_const _).aemeasurable
