import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin

noncomputable section

namespace GlobalTheory.Pdv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ColNorm : Prop :=
  ∀ a, B.R.m ≤ (I.cst a).A ∧ (I.cst a).M ≤ B.R.m ∧
    ∀ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1

variable (l : I.Laws) (Z : TC.Later B (I.cols l))

def stabStd (u : B.Word) (a : I.ι) : GlobalTheory.KerJ.StabDat ((I.rec7 l Z).chTw u a) := fun i c =>
  {g | ∃ s : (I.stp u a i).Stab c, g = ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
    B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL))}

def RdStd (u : B.Word) (a : I.ι) (r : KerRead ((I.rec7 l Z).chTw u a) B.fields) : Prop :=
  (∀ i c, r.N i c = ((I.stp u a i).rep c).1.1.deco.1.N) ∧
    ∀ i, i < B.R.m → ∀ c c' x, r.Xi i c c' x = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1
      ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)

def StdRd {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u a, ∃ r : KerRead ((I.rec7 l Z).chTw u a) B.fields, HEq (t.rd u a) r ∧ RdStd I l Z u a r

end GlobalTheory.Pdv

end
