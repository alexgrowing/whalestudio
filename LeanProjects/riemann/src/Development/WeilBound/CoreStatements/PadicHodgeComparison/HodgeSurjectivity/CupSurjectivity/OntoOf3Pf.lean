import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Tgt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.MkDat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SurjOfCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ontoOf3_pf : OntoOf3 := by
  intro hC hS hK hSq hD hF l _ K _ P M d hd hM hs hI n
  obtain ⟨S, hEt⟩ := hSq l K M d hd hM hs
  obtain ⟨Dt⟩ := mkDat hC hK hD P hd hM hs S hEt
  exact surj_of_core hC P M n fun a' x => ⟨Dt.N, Dt.hN, core hC hS P hM Dt (hF l K M hM _) hI x⟩

end CrystallineSemistableComparison.Onto

end
