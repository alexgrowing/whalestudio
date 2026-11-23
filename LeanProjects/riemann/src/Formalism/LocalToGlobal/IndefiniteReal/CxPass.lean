import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnit (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquiv (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), X.Θ t (X.jR t (A.fam.amb.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

def typeSp (gE : Representation ℂ G X.EE) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ X.EE :=
  ⨅ h : P, LinearMap.ker (gE (h : G) - (A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def EEg : Submodule ℂ X.EE :=
  LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def PrincipalInjectiveCommonRange : Prop :=
  Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def LevType (gE : Representation ℂ G X.EE) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  X.EEl b = EEg A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp A X gE P ψ

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

def CutPassage2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 T : Type) (m : ℕ) (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A.fam.Ok s → A.fam.TypesSep →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A.side P0 ψ0 X.zs).Pos → (A.side P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) → X.RATmu (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    GUnit A X gE → GEquiv A X gE →
    LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0 →
    LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1 →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

def CutPassage2S : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 T : Type) (m : ℕ) (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A.fam.Ok s → A.fam.TypesSep →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A.side P0 ψ0 X.zs).Pos → (A.side P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) → X.RATmu (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    GUnit A X gE → GEquiv A X gE →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.CxPass
