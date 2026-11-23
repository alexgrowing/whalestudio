import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  fun H => ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H).trans
    (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b _ c d _ _ _ _ => G Z hX Wt z a b c d)

end GlobalTheory.Mem.LiteralAutomorphy
