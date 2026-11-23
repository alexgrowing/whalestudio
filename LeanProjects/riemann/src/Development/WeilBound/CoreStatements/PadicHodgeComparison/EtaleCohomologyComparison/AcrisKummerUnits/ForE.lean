import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle

open CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.R.forE (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.E.RIn l :=
  ⟨fun _ h => h.splitUg, fun _ h => h.splitU, fun A => A.l_mem_nzd_U, fun _ h => h.idem, fun _ h => h.sharp_unit⟩
