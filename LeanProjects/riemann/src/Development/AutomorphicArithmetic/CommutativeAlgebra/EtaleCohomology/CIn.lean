import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.EndEx
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.BInEx
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.PinFixed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds

open CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

theorem cIn (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ)
    (hf : 0 < f) : CIn l K r f := by
  obtain ⟨N, h1, h2, F, h3⟩ := CrystallineSemistableComparison.crystallineComparison.pinEx l K r f hf
  obtain ⟨Amp, -, -, -, a1, a2, a3, a4, a5, -⟩ := CrystallineSemistableComparison.crystallineComparison.endEx (fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K) l K
  exact ⟨Amp, N, F, a1, a2, a3, a4, a5, h1, h2, fun M hM j => ⟨h3 M hM j, CrystallineSemistableComparison.crystallineComparison.bInEx l K M hM j⟩⟩

end UpperTheory.Ru.crystallineComparison
