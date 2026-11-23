import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagChar

theorem haarChar_det_mul_integral_comp_mulVec_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (m : MeasurableSpace (Fin N → k)) (hm : m = borel _)
    (ν : @Measure (Fin N → k) m) (hν : @Measure.IsAddHaarMeasure _ _ _ m ν)
    (T : GL (Fin N) k) (f : (Fin N → k) → ℂ) :
    ((distribHaarChar k (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have h2 : m = MeasurableSpace.pi := hm.trans (@BorelSpace.measurable_eq (Fin N → k) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst h2
  have hc := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin N => (Measure.addHaar : Measure k))
  rw [hc, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    ← GlobalTheory.WeilM.integral_comp_mulVec (Measure.addHaar : Measure k) T f, mul_smul_comm]

theorem nabs_det_mul_integral_comp_mulVec :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  intro F _ _ v N ν hν T f
  exact haarChar_det_mul_integral_comp_mulVec_localField (Fv F v) N _ rfl ν hν T f

end GlobalTheory.InertLagChar
