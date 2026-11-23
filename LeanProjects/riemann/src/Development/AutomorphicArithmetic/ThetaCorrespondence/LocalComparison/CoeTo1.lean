import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTiedOf6

noncomputable section

open Formalism.BasicNotions

def Formalism.BasicNotions.LocTied.to6 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI :=
  Classical.choice (UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T⟩)

def Formalism.BasicNotions.LocTied6.to1 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : LocTied l P AI :=
  Classical.choice (UpperTheory.Lit.Cmp.locTied_of6 l P AI ⟨T⟩)

instance UpperTheory.Lit.Cmp.coeTo6 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (LocTied l P AI) (LocTied6 l P AI) := ⟨LocTied.to6⟩

instance UpperTheory.Lit.Cmp.coeTo1 {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} :
    CoeTail (LocTied6 l P AI) (LocTied l P AI) := ⟨LocTied6.to1⟩

end
