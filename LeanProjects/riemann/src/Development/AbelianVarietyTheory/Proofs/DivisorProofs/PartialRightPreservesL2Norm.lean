import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C, hC⟩ := hT μ₂ inferInstance

  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : (κ ⊕ κ' → AF F) ≃ₜ+ (κ → AF F) × (κ' → AF F) :=
    { e.toEquiv with
      map_add' := fun _ _ => rfl
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  haveI : (μ.map eA).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ eA
  set c := (μ.map eA).addHaarScalarFactor (μ₁.prod μ₂)
  have hprod : μ.map eA = c • μ₁.prod μ₂ := Measure.isAddLeftInvariant_eq_smul _ _

  have key : ∀ g : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable g →
      ∫⁻ z, g z ∂μ = c * ∫⁻ a, ∫⁻ b, g (Sum.elim a b) ∂μ₂ ∂μ₁ := by
    intro g hg
    have h1 : ∫⁻ z, g z ∂μ = ∫⁻ p, g (e.symm p) ∂(μ.map eA) := by
      rw [show μ.map eA = μ.map e.toMeasurableEquiv from rfl, lintegral_map_equiv]
      refine lintegral_congr fun z => ?_
      exact congrArg g (e.symm_apply_apply z).symm
    rw [h1, hprod, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
      lintegral_prod (fun p => g (e.symm p)) (hg.comp e.symm.continuous.measurable).aemeasurable]
    rfl
  have hmeas : ∀ Φ ∈ schA F (κ ⊕ κ'), Measurable fun z => ‖Φ z‖ₑ ^ 2 := fun Φ hΦ =>
    ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ).measurable.enorm).pow_const 2
  refine ⟨C, fun Φ hΦ => ?_⟩
  have hslice : ∀ a : κ → AF F, (fun x => Φ (Sum.elim a x)) ∈ schA F κ' := fun a =>
    GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ
  have hin : ∀ a : κ → AF F, ∫⁻ b, ‖partR T Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ =
      C * ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ := fun a => hC _ (hslice a)
  have hm2 : Measurable fun a : κ → AF F => ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ :=
    ((hmeas Φ hΦ).comp e.symm.continuous.measurable).lintegral_prod_right'
  rw [key _ (hmeas _ (hmem Φ hΦ)), key _ (hmeas Φ hΦ)]
  simp_rw [hin]
  rw [lintegral_const_mul _ hm2, mul_left_comm]

end GlobalTheory.DblEval.L2RightPartial

end
