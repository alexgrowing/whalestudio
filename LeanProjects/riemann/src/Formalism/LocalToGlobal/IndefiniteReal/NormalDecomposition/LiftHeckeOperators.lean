import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.DecompOfNormalStatement
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.U2

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR.Cx Formalism.IndefR.CxPass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section Defs

variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3)

def liftHeckeOperators (j : Fin m) : (A3.liftI j A3.A.fam.μ0).OpIx → Module.End ℂ (X.FLC j A3.A.fam.μ0) :=
  fun i => X.opLC j A3.A.fam.μ0 (Sum.inl i)

def goodL (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (j : Fin m) :
    Submodule ℂ (X.FLC j A3.A.fam.μ0) :=
  X.goodPartComplexPoints (cvOf3 A3 P0 ψ0 P1 ψ1) false j A3.A.fam.μ0

def goodW (j : Fin m) : Submodule ℂ (X.W j) := LinearMap.range (X.w0C false j)

def IxL (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (j : Fin m) :
    Set ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :=
  Occ (liftHeckeOperators A3 X j) (goodL A3 X P0 ψ0 P1 ψ1 j)

def LiftedL (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (j : Fin m) :
    Set ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :=
  Lifted (hW j A3.A.fam.μ0) (goodW A3 X j) (IxL A3 X P0 ψ0 P1 ψ1 j)

def eigensystemChoice (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) :
    ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop :=
  fun j x => (fun i => A3.A.fam.v0.embedding (x i)) ∈ LiftedL A3 X P0 ψ0 P1 ψ1 hW j

def EigC (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) : Prop :=
  ∀ j, LiftsFull (X.θ' j A3.A.fam.μ0) (liftHeckeOperators A3 X j) (hW j A3.A.fam.μ0) (goodL A3 X P0 ψ0 P1 ψ1 j) (goodW A3 X j)
    (IxL A3 X P0 ψ0 P1 ψ1 j)

def OntoC (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) : Prop :=
  ∀ j, OntoParts (LinearMap.adjoint (X.θ' j A3.A.fam.μ0)) (liftHeckeOperators A3 X j) (hW j A3.A.fam.μ0) (goodL A3 X P0 ψ0 P1 ψ1 j)
    (goodW A3 X j) (IxL A3 X P0 ψ0 P1 ψ1 j)

end Defs

def EigCOfStatement : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gW : ∀ j, Representation ℂ G (X.W j)),
    DecompOfNormalStatement → A3.fam3.Ok3 s → X.KFormL → X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1) → X.RatZ →
    (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → HeckeIntertwiningLifts A3 X hW → LiftActionUnitary X gW →
    LiftGroupEquivariance A3 X gW → LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0 →
    OntoC A3 X P0 ψ0 P1 ψ1 hW → EigC A3 X P0 ψ0 P1 ψ1 hW

def ZeroEigenvalueCondition : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)),
    DecompOfNormalStatement → A3.fam3.Ok3 s → X.KFormL → X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1) →
    (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) →
    EigC A3 X P0 ψ0 P1 ψ1 hW → LiftsEig3 A3 X P0 ψ0 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW)

def ZeroTypeCondition : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)),
    HeckeIntertwiningLifts A3 X hW → X.PartsW false → LiftsTyp3 A3 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW)

end Formalism.IndefR.U2
