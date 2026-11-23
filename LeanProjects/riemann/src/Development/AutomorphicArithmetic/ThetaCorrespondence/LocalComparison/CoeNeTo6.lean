import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.CoeTo1

open Formalism.BasicNotions

instance UpperTheory.Lit.Cmp.coeNeTo6 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (Nonempty (LocTied l P AI)) (Nonempty (LocTied6 l P AI)) := ⟨UpperTheory.Lit.Cmp.locTied6 l P AI⟩

instance UpperTheory.Lit.Cmp.coeNeTo1 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (Nonempty (LocTied6 l P AI)) (Nonempty (LocTied l P AI)) := ⟨UpperTheory.Lit.Cmp.locTied_of6 l P AI⟩
