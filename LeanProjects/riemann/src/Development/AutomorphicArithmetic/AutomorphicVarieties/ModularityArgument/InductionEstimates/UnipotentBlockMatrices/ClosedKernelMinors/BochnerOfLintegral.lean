import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TowerPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CoordUnf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IwaInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem bochner_of_lintegral {ι Y P Q : Type*} [Countable ι] [MeasurableSpace Y] [MeasurableSpace P]
    [MeasurableSpace Q] (ν : Measure Y) (m : Measure P) (f : ι → Y → Q) (g : P → Q) (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) (c : ℝ) (hc : 0 ≤ c)
    (H : ∀ h : Q → ℝ≥0∞, Measurable h → ∫⁻ y, ∑' i, h (f i y) ∂ν = ENNReal.ofReal c * ∫⁻ p, h (g p) ∂m)
    (h : Q → ℂ) (hh : Measurable h) (hi : Integrable (fun p => h (g p)) m) :
    ∫ y, ∑' i, h (f i y) ∂ν = c * ∫ p, h (g p) ∂m := by
  have key : Measure.sum (fun i => ν.map (f i)) = ENNReal.ofReal c • m.map g := by
    refine Measure.ext_of_lintegral _ fun φ hφ => ?_
    rw [lintegral_sum_measure, lintegral_smul_measure, lintegral_map hφ hg, smul_eq_mul, ← H φ hφ,
      lintegral_tsum (f := fun i y => φ (f i y)) fun i => (hφ.comp (hf i)).aemeasurable]
    exact tsum_congr fun i => lintegral_map hφ (hf i)
  have h1 : Integrable h (m.map g) :=
    (integrable_map_measure hh.aestronglyMeasurable hg.aemeasurable).2 hi
  have h2 : Integrable h (Measure.sum fun i => ν.map (f i)) := by
    rw [key]; exact h1.smul_measure ENNReal.ofReal_ne_top
  have h3 : ∑' i, ∫⁻ y, ‖h (f i y)‖ₑ ∂ν ≠ ∞ := by
    have := h2.2.ne
    rw [lintegral_sum_measure] at this
    rwa [tsum_congr fun i => lintegral_map hh.enorm (hf i)] at this
  rw [integral_tsum (f := fun i y => h (f i y)) (fun i => (hh.comp (hf i)).aestronglyMeasurable) h3,
    ← integral_map hg.aemeasurable hh.aestronglyMeasurable,
    ← tsum_congr fun i => integral_map (hf i).aemeasurable hh.aestronglyMeasurable,
    ← integral_sum_measure h2, key, integral_smul_measure, ENNReal.toReal_ofReal hc, Complex.real_smul]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.unf :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure], (∃ c, Unf μ μ₂ κ c) ∧ 0 < volN K := by
  intro K _ _ μ _ μ₂ _ κ _
  refine ⟨?_, ?_⟩
  swap
  · rw [volN, Measure.real, unipMeasure_unipFundamentalDomain]; simp
  have hle : PK K ≤ Gam K (2 + 2) := Subgroup.map_subtype_le _
  haveI : DiscreteTopology (PK K) := DiscreteTopology.of_subset (s := (Gam K (2 + 2) : Set (G1 K (2 + 2))))
    (inferInstanceAs (DiscreteTopology (Gam K (2 + 2)))) hle
  obtain ⟨E, hE, hEu⟩ := exists_fundamentalDomain (PK K)
  obtain ⟨c, hc, hI⟩ := iwaInt μ μ₂ κ
  have hL : ∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
      ∫⁻ y, ∑' q : Cos K, Ψ ((q.out : G1 K (2 + 2)) * y) ∂fd μ = ENNReal.ofReal c * ∫⁻ p, Ψ (pt p) ∂parM μ₂ κ := by
    intro Ψ hΨ hinv
    rw [tower μ E hE hEu Ψ hΨ hinv, ← coordUnf μ₂ κ E hE hEu Ψ hΨ hinv, ← hI _ (hΨ.indicator hE),
      lintegral_indicator hE]
  refine ⟨c, hc, hL, fun Ψ hΨ hinv hint => ?_⟩
  have hpt : Measurable (pt (K := K)) := by
    haveI : OpensMeasurableSpace (G1 K 2 × ℝ) := inferInstance
    haveI : OpensMeasurableSpace (G1 K 2 × G1 K 2 × ℝ) := inferInstance
    have h1 := ((blkLaws (K := K)).2.2.2.1).measurable
    have h2 : Measurable (unipOne K (2 + 2) 2) := (continuous_unipOne 2).measurable
    have h3 : Measurable fun p : Par K => (p.1, p.2.1, p.2.2.1) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)
    exact ((h2.comp measurable_snd.snd.snd.snd).mul (h1.comp h3)).mul
      (measurable_subtype_coe.comp measurable_snd.snd.snd.fst)
  have hmk : Measurable (mk (PK K)) := measurable_quotient_mk''
  let h : RightCosetSpace (PK K) → ℂ := Quotient.lift Ψ fun a b hab => by
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 hab
    rw [← hγ]
    exact hinv γ γ.2 b
  have hh : Measurable h := measurable_from_quotient.2 hΨ
  exact bochner_of_lintegral (fd μ) (parM μ₂ κ) (fun (q : Cos K) y => mk (PK K) ((q.out : G1 K (2 + 2)) * y))
    (fun p => mk (PK K) (pt p)) (fun q => hmk.comp (measurable_const_mul _)) (hmk.comp hpt) c hc.le
    (fun φ hφ => hL (fun g => φ (mk (PK K) g)) (hφ.comp hmk) fun γ hγ g => by simp only [mk_mul_of_mem hγ])
    h hh hint
