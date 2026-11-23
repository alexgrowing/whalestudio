import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.IsLocallyConstantHeisenbergLatticeVacuumFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrSBFin
open _root_.GlobalTheory

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_add_right w.1)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end Tw.SchrSBFin
