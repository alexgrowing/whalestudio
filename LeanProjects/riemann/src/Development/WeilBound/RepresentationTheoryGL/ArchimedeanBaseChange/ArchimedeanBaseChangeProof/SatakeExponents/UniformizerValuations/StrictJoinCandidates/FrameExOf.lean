import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def FixFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n) (w : Pl E)
  (K : Subgroup (GLw n w)), IsOpen (K : Set (GLw n w)) → IsCompact (K : Set (GLw n w)) →
  FiniteDimensional ℂ ↥(fixed (Tail.prodAt D w) K)

def FrameExOf : Prop := USide → Eig.SphOne → Eig.SpecTrace → Eig.DiagAlg → Inert.InertPlaceEx → Inert.WittEx → Inert.SatEx →
  Inert.UnifOf → InertInSec → LoneId → ConeEig → SatCompAt → CandIndep → CandFin → FixFin → Choice.ChoiceT →
  Choice.ChoiceS → Choice.ChoiceM → Choice.ShufEx → Choice.VResStd → Choice.ShufStd → Choice.ConeTwo → Tail.TargetAlg →
  Tail.MonoRes → FrameEx

end PositivityTheory.Rg.BcB.F.FX

end
