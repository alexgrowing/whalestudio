import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MemIntPolOfCoeff
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SatBlock
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CharZeroOfW
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def RestKapNum : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restBlockForm_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hK : RestKapNum) : RestBlockForm := by
  have h17 : TransportedAlt fun _ _ _ _ _ _ _ _ Cm _ => (17 : ℝ) ≤ Cm :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun _ _ _ _ _ => 1)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ => h
  refine TransportedAlt.mono ?_ ((thr_std.and h17).and hK)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨_, hstd⟩, hCm⟩, hKa⟩
  exact blockFormAt_of hCm hstd ioFockAt eigAt (homAt _ _ _ _ _ _ _ _ _) dvdAt satAt (gThetaAt D)
    (factAt_of h52 (kapAt_of hKa))

end Formalism.MainNotions.ColumnSystems.Pf
