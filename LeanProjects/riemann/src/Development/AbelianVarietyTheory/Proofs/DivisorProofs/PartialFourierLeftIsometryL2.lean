import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem partL_lintegral_sq : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL (κ' := κ') A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hA μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL (κ' := κ') A Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ =
      C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ := by
    intro y
    have h := hC₁ _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
    simpa only [partL_apply, Sum.elim_comp_inl, Sum.elim_comp_inr] using h
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DoublingEvaluationL2

end
