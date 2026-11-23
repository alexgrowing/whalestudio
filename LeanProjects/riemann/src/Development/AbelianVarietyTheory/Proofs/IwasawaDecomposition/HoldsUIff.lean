import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

abbrev DatP : Type 1 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl), R3.Dat (w.st Z) w.I hX T Wt → Prop

def AtDat (P : DatP) : Prop :=
  StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt),
    GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → P K B f T w Z hX Wt z

theorem AtDat.and {P Q : DatP} (hP : AtDat P) (hQ : AtDat Q) :
    AtDat fun K B f T w Z hX Wt z => P K B f T w Z hX Wt z ∧ Q K B f T w Z hX Wt z :=
  (StepW.and hP hQ).trans (StepW.of_all fun _ _ _ _ _ _ _ H Z hX Wt z a b c d =>
    ⟨H.1 Z hX Wt z a b c d, H.2 Z hX Wt z a b c d⟩)

end GlobalTheory.Mem.Top.Bl

end
