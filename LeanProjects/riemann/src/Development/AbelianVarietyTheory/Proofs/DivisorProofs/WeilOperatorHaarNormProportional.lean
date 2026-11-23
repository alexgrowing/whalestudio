import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem lintegral_sq_split {Z X Y : Type} [TopologicalSpace Z] [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X]
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : Z ≃ₜ X × Y) (he : ∀ a b, e (a + b) = e a + e b)
    (μ : Measure Z) [μ.IsAddHaarMeasure] (μX : Measure X) [μX.IsAddHaarMeasure]
    {f g : Z → ℂ} (hf : Continuous f) (hg : Continuous g) (c : ℝ≥0∞)
    (h : ∀ y, ∫⁻ x, ‖f (e.symm (x, y))‖ₑ ^ 2 ∂μX = c * ∫⁻ x, ‖g (e.symm (x, y))‖ₑ ^ 2 ∂μX) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = c * ∫⁻ z, ‖g z‖ₑ ^ 2 ∂μ := by
  let E : Z ≃ₜ+ X × Y :=
    { e.toEquiv with
      map_add' := he
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let eM : Z ≃ᵐ X × Y := e.toMeasurableEquiv
  let μY : Measure Y := Measure.addHaar
  haveI hν : (μ.map E).IsAddHaarMeasure := inferInstance
  have hE : (E : Z → X × Y) = eM := rfl
  set s := Measure.addHaarScalarFactor (μ.map E) (μX.prod μY)
  have hs : μ.map E = s • (μX.prod μY) := Measure.isAddLeftInvariant_eq_smul _ _
  have key : ∀ F : Z → ℂ, Continuous F →
      ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
    intro F hF
    have hm : Measurable fun p : X × Y => ‖F (e.symm p)‖ₑ ^ 2 :=
      ((hF.comp e.symm.continuous).measurable.enorm.pow_const 2)
    calc ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = ∫⁻ p, ‖F (e.symm p)‖ₑ ^ 2 ∂(μ.map E) := by
          rw [hE, lintegral_map_equiv]; simp [eM]
      _ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
          rw [hs, lintegral_smul_measure, lintegral_prod_symm _ hm.aemeasurable]; rfl
  rw [key f hf, key g hg]
  have hmg : Measurable fun p : X × Y => ‖g (e.symm p)‖ₑ ^ 2 :=
    ((hg.comp e.symm.continuous).measurable.enorm.pow_const 2)
  simp_rw [h]
  rw [lintegral_const_mul _ (hmg.lintegral_prod_left' )]
  ring

end GlobalTheory.DoublingEvaluationL2

namespace GlobalTheory.DoublingEvaluationL2

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  intro F _ _ κ κ' _ _ A hA hL2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  let μX : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc⟩ := hL2 μX inferInstance
  constructor
  · intro μ hμ
    letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
    haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_left F κ κ κ' A hA) Φ hΦ
    refine lintegral_sq_split (Homeomorph.sumPiEquivProdPi κ κ' (fun _ => AF F)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
  · intro μ hμ
    letI mZ : MeasurableSpace (κ' ⊕ κ → AF F) := borel _
    haveI : BorelSpace (κ' ⊕ κ → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_right F κ' κ κ A hA) Φ hΦ
    refine lintegral_sq_split ((Homeomorph.sumPiEquivProdPi κ' κ (fun _ => AF F)).trans
        (Homeomorph.prodComm _ _)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceR hΦ y)

end GlobalTheory.DoublingEvaluationL2
