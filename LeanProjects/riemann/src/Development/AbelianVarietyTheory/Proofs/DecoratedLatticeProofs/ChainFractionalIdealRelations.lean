import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

theorem step (D : D7) {j : ℕ} (h : j + 1 + 1 ≤ D.R.m) :
    D.host.AA⁻¹ * (dI D * cI D j) = D.host.AA * cI D (j + 1 + 1) ∧
    D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
  obtain ⟨-, hA, hB, -⟩ := host_ne_zero D
  have e1 : D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
    rw [dI]
    calc D.host.AA⁻¹ * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar * cI D j)
        = (D.host.AA⁻¹ * D.host.AA) * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_mul]
  refine ⟨?_, e1⟩
  rw [e1]
  have hs := cI_step D h
  calc FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j
      = D.host.AAbar * (FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j) := by ring
    _ = D.host.AAbar * (D.host.AA * D.host.AAbar⁻¹ * cI D (j + 1 + 1)) := by rw [hs]
    _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA * cI D (j + 1 + 1)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hB, one_mul]

end GlobalTheory.SeeSaw.ChainIdeals
