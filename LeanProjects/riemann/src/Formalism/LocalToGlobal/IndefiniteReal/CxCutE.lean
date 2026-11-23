import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section CutE

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def LiftsEig (P : Subgroup G) (ψ : P →* Kˣ) (C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop) : Prop :=
  ∀ j, (A.fam.L j A.fam.μ0).Z0 (A.fam.lvlA P ψ) (X.Zl j A.fam.μ0) =
    (A.fam.L j A.fam.μ0).inV0 (A.fam.lvlA P ψ) (Formalism.L2.Col.eigSum (A.fam.L j A.fam.μ0).op (C j))

def LiftsTyp (C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop) : Prop :=
  ∀ j x, C j x → A.fam.IsType (A.fam.L j A.fam.μ0) (A.fam.tr j) x

def HeckeRatR : Prop := (A.fam.R A.fam.μ0).OkH

def HeckeRatL : Prop := ∀ j : Fin m, (A.fam.L j A.fam.μ0).OkH

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

def CutProviso : Prop :=
  ∀ (s : ℕ) (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop),
    A.fam.Ok s → HeckeRatL A → LiftsEig A X P0 ψ0 C0 → LiftsEig A X P1 ψ1 C1 →
      ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Proviso

def CutTypes : Prop :=
  ∀ (s : ℕ) (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop),
    A.fam.Ok s → A.fam.TypesSep → X.zs.Stable → LiftsEig A X P0 ψ0 C0 → LiftsEig A X P1 ψ1 C1 →
      LiftsTyp A C0 → LiftsTyp A C1 → ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Types

def CutPartsOrth : Prop :=
  ∀ s : ℕ, A.fam.Ok s → HeckeRatR A → X.zs.Stable → ∀ b, X.PartsOrth b (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

end CutE

end Formalism.IndefR.Cx
