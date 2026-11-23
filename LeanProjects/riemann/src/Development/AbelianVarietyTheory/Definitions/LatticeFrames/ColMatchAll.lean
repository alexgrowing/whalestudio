import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)

abbrev ColsK : Type := MfV (Pr := B.primes X) B.wts I.Ch u

abbrev RowsK : Type := MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps

structure CplData where

  b : (I.idx a).β (B.R.m - 2 + 1)
  hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b
  hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps
  hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok

abbrev RamH (hX : B.fields.Ok) : HLat B.fields.K := MramH (Pr := B.primes X) B.wts I.Ch hX u

abbrev RowH (hX : B.fields.Ok) : HLat B.fields.K := MtildeH (Pr := B.primes X) B.wts I.Ch hX I.sel (I.tup a) I.Ps

variable {I u a}

def CplData.per (c : CplData I u a) (h : I.Ok) (hX : B.fields.Ok) :
    ColsK I u →ₗ[B.fields.K] RowsK I a →ₗ[B.fields.K] B.fields.K :=
  PtilE (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u ∘ₗ
    colMu (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) c.b c.hY I.Ps c.hK c.hF (h.idx_ok a)

def CplData.phi (c : CplData I u a) (h : I.Ok) (hX : B.fields.Ok) :
    (RamH I u hX).V →ₗ[B.fields.K] Module.Dual B.fields.K (RowH I a hX).V :=
  GlobalTheory.CoreHt.phiCol (Pr := B.primes X) B.wts I.Ch hX I.sel (I.tup a) (I.cst a) (I.idx a)
    (chKerC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) c.b c.hY I.Ps c.hK) c.hF (h.idx_ok a)

theorem CplData.phi_apply (c : CplData I u a) (h : I.Ok) (hX : B.fields.Ok) (x : (RamH I u hX).V) (z : RowsK I a) :
    c.phi h hX x z = c.per h hX x.1 z := rfl

variable (I u a) (l : I.Laws)

def IsCol (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) : Prop :=
  ∀ c : (I.stp u a 0).Cl, x.1 c = φ.1 ((I.stp u a 0).rep c).1.1.deco

def IsRow (F : (I.per l u a).Mt) (z : RowsK I a) : Prop :=
  ∀ p : (I.stX a).D (), F.1 () p = MvPolynomial.map B.embLL (z.1 (toRow I.sel (I.tup a) p.1.1)).1

def ColMatch (h : I.Ok) (hX : B.fields.Ok) : Prop :=
  Nonempty (CplData I u a) ∧ ∀ (c : CplData I u a) x φ F z, IsCol I u a l x φ → IsRow I u a l F z →
    (I.per l u a).PtilCol ((I.fm l u a).emb 0 x) F = B.embLL (c.per h hX φ z)

def ColMatchAll : Prop :=
  ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (_Z : TC.Later B (I.cols l)),
    ColIn.JetsIn I → ∀ u a, ColMatch I u a l h hX

end GlobalTheory.Core.Ht2

end
