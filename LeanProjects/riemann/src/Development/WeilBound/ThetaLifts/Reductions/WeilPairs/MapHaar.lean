import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_haar {nS nT N : ℕ} (α : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (hαc : Continuous α)
    (hαs : Continuous α.symm) (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure)
    (μN : Measure (Fin N → AF F)) (hμN : μN.IsAddHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧ (∀ G : (Fin N → AF F) → ℂ, ∫ v, G (α v) ∂ν = (c : ℂ) * ∫ x, G x ∂μN) ∧
      ∀ G : (Fin N → AF F) → ℂ, Integrable (fun v => G (α v)) ν ↔ Integrable G μN := by
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI := hν
  haveI := hμN
  let a : WOF F E nS nT ≃ₜ (Fin N → AF F) :=
    { toEquiv := α.toEquiv, continuous_toFun := hαc, continuous_invFun := hαs }
  let m : WOF F E nS nT ≃ᵐ (Fin N → AF F) := a.toMeasurableEquiv
  have hm : ∀ v, m v = α v := fun _ => rfl
  haveI : ContinuousAdd (WOF F E nS nT) := ⟨by
    have h : (fun p : WOF F E nS nT × WOF F E nS nT => p.1 + p.2) = fun p => α.symm (α p.1 + α p.2) := by
      funext p; simp
    rw [h]
    exact hαs.comp ((hαc.comp continuous_fst).add (hαc.comp continuous_snd))⟩
  haveI : ContinuousNeg (WOF F E nS nT) := ⟨by
    have h : (fun x : WOF F E nS nT => -x) = fun x => α.symm (-α x) := by
      funext x; simp
    rw [h]
    exact hαs.comp hαc.neg⟩
  haveI hmap : (Measure.map α ν).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν α.toAddEquiv hαc hαs
  have hmm : Measure.map m ν = Measure.map α ν := rfl
  set c := Measure.addHaarScalarFactor (Measure.map α ν) μN with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have heq : Measure.map α ν = c • μN := by
    first
    | exact Measure.isAddHaarMeasure_eq_smul _ _
    | exact Measure.isAddLeftInvariant_eq_smul _ _
    | exact Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  have heq' : Measure.map α ν = (c : ENNReal) • μN := by
    rw [heq]
    rfl
  refine ⟨c, hc, fun G => ?_, fun G => ?_⟩
  · have h1 : ∫ v, G (α v) ∂ν = ∫ x, G x ∂(Measure.map m ν) := (integral_map_equiv m G).symm
    rw [h1, hmm, heq', integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  · have h1 : Integrable (fun v => G (α v)) ν ↔ Integrable G (Measure.map m ν) :=
      (integrable_map_equiv m G).symm
    rw [h1, hmm, heq']
    exact integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
