import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.InfMatchOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gelfand_value_at_zero_const {n : ℕ} (x y : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal x 0 = GlobalTheory.Dec.gelfVal y 0 := by
  simp only [GlobalTheory.Dec.gelfVal, pow_zero]

theorem UpperTheory.BaseChangeIdentities.GelfandReading.pInfMatch :
    UpperTheory.BaseChangeIdentities.GelfandReading.InfMatchOf := by
  intro hG E _ _ _ a χ χ' h
  funext τ
  unfold mOf
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · refine hG a _ _ fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact gelfand_value_at_zero_const _ _
    · exact h _ _ m hm ha

end
