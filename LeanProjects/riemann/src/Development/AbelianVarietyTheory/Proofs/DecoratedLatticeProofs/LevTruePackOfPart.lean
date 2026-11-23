import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroNe

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest

theorem isTypePlaces_vGs {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (h : I.Ok) :
    GlobalTheory.Core.Mi.IsTypePlaces (D := I.rec7 l Z) (B.primes X).vGs := by
  classical
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit (I.rec7 l Z) (TC.cf I l Z)
  have hP : L.Pg = (B.primes X).vGs := by
    ext w
    rw [hL.Pg w, hC]
    have hv : w ∈ (B.primes X).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
      rw [← h.pibar 0 w, ← h.pibar 1 w]
      exact @Finset.mem_union _ (_) _ _ _
    exact (hv.trans (Fin.exists_fin_two (p := fun k => I.C.P.Div k w)).symm).symm
  rw [← hP]
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh hL

end GlobalTheory.Fam.ColTest

end
