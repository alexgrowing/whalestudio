import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem map_right_inv {A H C : Type} [Group A] [Group H] [Group C] [MeasurableSpace A] [MeasurableSpace H]
    [MeasurableSpace C] (κ : Measure A) (ν : Measure H) [SFinite κ] [SFinite ν] (p : A × H → C) (hp : Measurable p)
    (hm : Measurable fun x : C × C => x.1 * x.2) (hs : Function.Surjective p) (hmul : ∀ x y, p x * p y = p (x * y))
    (hκ : ∀ a, MeasurePreserving (· * a) κ κ) (hν : ∀ d, MeasurePreserving (· * d) ν ν) (u : C) :
    MeasurePreserving (· * u) (Measure.map p (κ.prod ν)) (Measure.map p (κ.prod ν)) := by
  obtain ⟨⟨a, d⟩, rfl⟩ := hs u
  have hu : Measurable fun c : C => c * p (a, d) := hm.comp (measurable_id.prodMk measurable_const)
  refine ⟨hu, ?_⟩
  have hq := (hκ a).prod (hν d)
  rw [Measure.map_map hu hp]
  have e : (fun c : C => c * p (a, d)) ∘ p = p ∘ Prod.map (· * a) (· * d) := by
    funext x
    exact hmul x (a, d)
  rw [e, ← Measure.map_map hp hq.measurable, hq.map_eq]

theorem UpperTheory.haar_decomposition_norm_one_gl2 :
    ∀ {K : Type} [Field K] [NumberField K] (κ₂ : Measure (archCompact K 2)), IsHaarK κ₂ → ∃ (ν : Measure (AdelicGLn.integralFiniteGL K 2)) (ρ : Measure (KG K 2)), IsProbabilityMeasure ν ∧ ν.IsOpenPosMeasure ∧ IsProbabilityMeasure ρ ∧ (∀ u : KG K 2, MeasurePreserving (· * u) ρ ρ) ∧ ∀ F : G1 K 2 → ℂ, (Continuous fun k : KG K 2 => F k) → ∫ v, F (v : G1 K 2) ∂ρ = ∫ a, ∫ d, F (arc1 a * fin1 (d : FA K 2)) ∂ν ∂κ₂ := by
  intro K _ _ κ₂ hκ
  haveI := hκ.prob
  obtain ⟨α, β, -, -, hdec, -, hA, hF⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
  obtain ⟨-, -, hcomm, harc, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := K) 2 ∅

  let ν₀ : Measure (AdelicGLn.integralFiniteGL K 2) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν₀ := ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (AdelicGLn.integralFiniteGL K 2)))⟩
  let ν : Measure (AdelicGLn.integralFiniteGL K 2) := ν₀.inv
  haveI hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have hνo : ν.IsOpenPosMeasure := continuous_inv.isOpenPosMeasure_map inv_surjective
  have hνr : ∀ d, MeasurePreserving (· * d) ν ν := fun d => measurePreserving_mul_right ν d

  let p : archCompact K 2 × AdelicGLn.integralFiniteGL K 2 → KG K 2 := fun x =>
    ⟨arc1 x.1 * fin1 (x.2 : FA K 2), (KG K 2).mul_mem (hA x.1) (hF x.2)⟩
  have hpc : Continuous p := Continuous.subtype_mk ((harc.comp continuous_fst).mul
    (MultiplicityOne.continuous_finProj.comp (continuous_subtype_val.comp continuous_snd))) _
  have hpm : Measurable p := hpc.measurable
  have hps : Function.Surjective p := fun k => ⟨(α k, β k), Subtype.ext (hdec k).symm⟩
  have hmul : ∀ x y, p x * p y = p (x * y) := by
    intro x y
    apply Subtype.ext
    change arc1 x.1 * fin1 (x.2 : FA K 2) * (arc1 y.1 * fin1 (y.2 : FA K 2)) =
      arc1 (x.1 * y.1) * fin1 ((x.2 * y.2 : AdelicGLn.integralFiniteGL K 2) : FA K 2)
    have e1 : arc1 (x.1 * y.1) = arc1 x.1 * arc1 y.1 := by simp [arc1]
    have e2 : fin1 ((x.2 * y.2 : AdelicGLn.integralFiniteGL K 2) : FA K 2) = fin1 (x.2 : FA K 2) * fin1 (y.2 : FA K 2) := by
      simp [fin1]
    rw [e1, e2, mul_assoc, mul_assoc, ← mul_assoc (fin1 (x.2 : FA K 2)), (hcomm y.1 (x.2 : FA K 2)).symm.eq, mul_assoc]
  haveI : IsProbabilityMeasure (κ₂.prod ν) := inferInstance
  refine ⟨ν, Measure.map p (κ₂.prod ν), hνp, hνo, Measure.isProbabilityMeasure_map hpm.aemeasurable,
    map_right_inv κ₂ ν p hpm (continuous_mul.measurable) hps hmul hκ.right hνr, ?_⟩
  intro F hFc
  have hc : Continuous fun x => F (p x : G1 K 2) := hFc.comp hpc
  rw [integral_map hpm.aemeasurable hFc.aestronglyMeasurable,
    integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
