import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.PairingCommutesLiftOperators
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.Decomp
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.U2

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR.Cx Formalism.IndefR.CxPass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def UnitaryTwoStatement : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gW : ∀ j, Representation ℂ G (X.W j)),
    A3.fam3.Ok3 s → X.KFormL → X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1) → X.RatZ →
    (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → HeckeIntertwiningLifts A3 X hW → LiftActionUnitary X gW →
    LiftGroupEquivariance A3 X gW → LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0 →
    X.PartsW false → OntoC A3 X P0 ψ0 P1 ψ1 hW →
    LiftsEig3 A3 X P0 ψ0 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW) ∧ LiftsTyp3 A3 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW)

theorem u2 : @UnitaryTwoStatement K _ _ _ G _ _ Pl0 I0 Ty T m := by
  intro A3 X s P0 ψ0 P1 ψ1 Dc Sp Zsc hW gW hOk hKL hJL hRZ hOkH hHT hGU hGE hLev hParts hOnto
  have hEigC := eigCOf A3 X s P0 ψ0 P1 ψ1 Dc Sp Zsc hW gW decompOfNormal hOk hKL hJL hRZ hOkH hHT hGU hGE
    hLev hOnto
  exact ⟨eig0Of A3 X s P0 ψ0 P1 ψ1 hW decompOfNormal hOk hKL hJL hOkH hEigC,
    typ0Of A3 X P0 ψ0 P1 ψ1 hW hHT hParts⟩

def UnitaryTwoPackageStatement : Prop :=
  ∀ (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gW : ∀ j, Representation ℂ G (X.W j)),
    A3.fam3.Ok3 s → X.KFormR → X.KFormL → X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1) → X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1) →
    Formalism.IndefR.Rat.RowTest X → Formalism.IndefR.Rat.LiftTest X →
    (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → HeckeIntertwiningLifts A3 X hW → LiftActionUnitary X gW →
    LiftGroupEquivariance A3 X gW → LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0 →
    X.PartsW false → OntoC A3 X P0 ψ0 P1 ψ1 hW →
    LiftsEig3 A3 X P0 ψ0 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW) ∧ LiftsTyp3 A3 (eigensystemChoice A3 X P0 ψ0 P1 ψ1 hW)

theorem unitary_two_package : @UnitaryTwoPackageStatement K _ _ _ G _ _ Pl0 I0 Ty T m := by
  intro A3 X s P0 ψ0 P1 ψ1 Dc Sp Zsc hW gW hOk hKR hKL hJR hJL hRow hLift hOkH hHT hGU hGE hLev hParts hOnto
  exact u2 A3 X s P0 ψ0 P1 ψ1 Dc Sp Zsc hW gW hOk hKL hJL
    (Formalism.IndefR.Rat.ratZOfTests X (cvOf3 A3 P0 ψ0 P1 ψ1) hKR hKL hJR hJL hRow hLift)
    hOkH hHT hGU hGE hLev hParts hOnto

end Formalism.IndefR.U2
