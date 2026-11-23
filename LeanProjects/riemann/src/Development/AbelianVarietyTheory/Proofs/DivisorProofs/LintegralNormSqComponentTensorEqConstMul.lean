import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlaceStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.AdelicPush

open GlobalTheory.AdelicU

theorem lintegral_tens_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v r hr hinv μA hμA μ hμ K hK hKi hK0 hKt
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have hcont : Continuous (evFin F v) := by
    change Continuous fun a => _
    exact (PI.LevelKSplit.W.Cont.continuous_evalV v).comp continuous_snd
  let evK : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevKm : Measurable evK := (continuous_pi fun i => hcont.comp (continuous_apply i)).measurable
  let ρ : (κ → AF F) → ENNReal := fun x => ‖r x‖ₑ ^ 2
  have hρ : Measurable ρ := hr.enorm.pow_const 2
  let ν : Measure (κ → Fv F v) := (μA.withDensity ρ).map evK
  have hνA : ∀ A, MeasurableSet A → ν A = ∫⁻ x, A.indicator 1 (evK x) * ρ x ∂μA := by
    intro A hA
    rw [Measure.map_apply hevKm hA, withDensity_apply _ (hevKm hA), ← lintegral_indicator (hevKm hA)]
    refine lintegral_congr fun x => ?_
    by_cases h : evK x ∈ A <;> simp [Set.indicator, h]
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro y
    ext A hA
    rw [Measure.map_apply (measurable_const_add y) hA, hνA _ hA, hνA _ (measurable_const_add y hA)]
    let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
    have hev : ∀ x, evK (x + z) = y + evK x := fun x => funext fun i => by
      simp [evK, z, GlobalTheory.LatVac.evFin_liftV, add_comm]
    rw [← lintegral_add_right_eq_self (fun x => A.indicator 1 (evK x) * ρ x) z]
    refine lintegral_congr fun x => ?_
    simp only [hev, ρ, hinv x z hz]
    by_cases h : y + evK x ∈ A <;> simp [Set.indicator, h]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  haveI : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν K hK hKi
    (by rw [hνA K hKm]; exact hK0) (by rw [hνA K hKm]; exact hKt)
  have hsc : ∀ s : Set (κ → Fv F v), IsCompact (closure s) →
      ν s = (Measure.addHaarScalarFactor ν μ : ENNReal) * μ s := fun s hs => by
    rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ hs, ENNReal.smul_def, smul_eq_mul]
  refine ⟨(Measure.addHaarScalarFactor ν μ : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    have := hsc K (by rw [hK.isClosed.closure_eq]; exact hK)
    rw [h0, zero_mul, hνA K hKm] at this
    exact hK0 this
  intro φ hφ hφc
  set C : ENNReal := (Measure.addHaarScalarFactor ν μ : ENNReal)
  let T := tsupport φ
  have hrest : ν.restrict T = C • μ.restrict T := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hsc _ (hφc.isCompact.of_isClosed_subset isClosed_closure
      (closure_minimal Set.inter_subset_right (isClosed_tsupport φ)))
  have hf : Measurable fun y => ‖φ y‖ₑ ^ 2 := hφ.measurable.enorm.pow_const 2
  have hsupp : Function.support (fun y => ‖φ y‖ₑ ^ 2) ⊆ T := by
    intro y hy
    by_contra h
    exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
  calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA
      = ∫⁻ x, (ρ * fun x => (fun y => ‖φ y‖ₑ ^ 2) (evK x)) x ∂μA := by
        refine lintegral_congr fun x => ?_
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.mul_apply, ρ, evK, enorm_mul, mul_pow, mul_comm]
    _ = ∫⁻ x, (fun y => ‖φ y‖ₑ ^ 2) (evK x) ∂(μA.withDensity ρ) :=
        (lintegral_withDensity_eq_lintegral_mul _ hρ (hf.comp hevKm)).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂ν := (lintegral_map hf hevKm).symm
    _ = ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂ν := (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(C • μ.restrict T) := by rw [hrest]
    _ = C * ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂μ := lintegral_smul_measure _ _
    _ = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by rw [setLIntegral_eq_of_support_subset hsupp]

end GlobalTheory.AdelicPush

end
