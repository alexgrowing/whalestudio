import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colPt (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    GA D (G.pS (.top t (lastIx D))) × GA D (G.pT (.top t (lastIx D))) :=
  G.toPair (.top t (lastIx D)) 1 (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1

theorem colShift_eq (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    colShift S t g = W.om _ (colPt S t g) := rfl

def rowPt (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    GA D (G.pS (.chi (lastIx D) D.R.m : Pair T)) × GA D (G.pT (.chi (lastIx D) D.R.m : Pair T)) :=
  G.toPair (.chi (lastIx D) D.R.m) 1 (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1

theorem rowShift_eq (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    rowShift S k = W.om (.chi (lastIx D) D.R.m) (rowPt S k) := rfl

def stdLat (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True

end GlobalTheory.LastVertexMove

namespace GlobalTheory.LastVertexMove

variable {D : D7}

def moveFn {A B : HSp D} (q : GA D A × GA D B) (Φ : WO A B → ℂ) : WO A B → ℂ := fun x => Φ (actO A B q.1⁻¹ q.2⁻¹ x)

end GlobalTheory.LastVertexMove
