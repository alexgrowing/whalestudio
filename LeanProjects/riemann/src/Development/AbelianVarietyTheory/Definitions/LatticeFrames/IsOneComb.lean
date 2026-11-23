import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def IsOneComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) (L : Level (GL (n ⊕ Fin c) k)) (α : GL (n ⊕ Fin c) k)
    (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A), IsSmoothRep σ →
    ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∀ v : A, (∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) v = (L.lam j : ℂ) • v) →
      toOne ν σ P l (σ α v) = GlobalTheory.PosOne.comb e fun g => l (σ g v)

end Local

def conv {G : Type} [Monoid G] (l : List (G →₀ ℂ)) : G →₀ ℂ :=
  l.foldr (fun e r => e.sum fun g a => r.sum fun h b => Finsupp.single (g * h) (a * b)) (Finsupp.single 1 1)

def aconv {G : Type} [AddMonoid G] (l : List (G →₀ ℂ)) : G →₀ ℂ :=
  l.foldr (fun e r => e.sum fun g a => r.sum fun h b => Finsupp.single (g + h) (a * b)) (Finsupp.single 0 1)

variable {D : D7}

structure Dbl2 (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) where
  B : BesLev D (σ + 1)
  J : JacLev D (σ + 1)
  B' : BesLev D σ
  s₁ : StepBF ψ B J
  s₂ : StepFB ψ J B'
  l : Link B B'.L B'.ζ
  vL : VolM D B'.L.rank J.W₀.rank
  χ₁ : (AE D)ˣ →* Circle
  χ₂ : (AE D)ˣ →* Circle
  χz : (AE D)ˣ →* Circle
  oma : Om B.A J.W₀
  omb : Om J.W₀ B'.A
  V₁ : s₁.χV = χ₁ * χz
  W₁ : s₁.χW = χ₁
  V₂ : s₂.χV = χ₂
  W₂ : s₂.χW = χ₂ * χz
  weila : IsWeilDatumO ψ B.A J.W₀ χ₁ χ₁ oma
  weilb : IsWeilDatumO ψ J.W₀ B'.A χ₂ χ₂ omb

variable {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

def Dbl2.con (S : Dbl2 ψ σ) (Φ₁ : WO S.B.V S.J.W → ℂ) (Φ₂ : WO S.J.W S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W)
    (h₂ : GA D S.B'.V) : WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ :=
  GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ (S.s₁.om (g, h₁) Φ₁)) (flatFB S.s₂ (S.s₂.om (h₁, h₂) Φ₂))

def Dbl2.val (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Φ₁ : WO S.B.V S.J.W → ℂ)
    (Φ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W)
    (h₂ : GA D S.B'.V) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂ (S.con Φ₁ Φ₂ g h₁ h₂))) (rTrans h₂ f)

set_option maxHeartbeats 2000000 in

structure QStep (S : Dbl2 ψ σ) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  ψk : AddChar k Circle
  char : (ofSplit q).IsChar ψ ψk
  cond : HasConductor ψk 1
  n₀ : Type
  n₁ : Type
  n₂ : Type
  [f₀ : Fintype n₀]
  [e₀' : DecidableEq n₀]
  [f₁ : Fintype n₁]
  [e₁' : DecidableEq n₁]
  [f₂ : Fintype n₂]
  [e₂' : DecidableEq n₂]
  c : ℕ
  F : Dbl (ofSplit q) S.B S.J S.B' n₀ n₁ n₂ c
  gl₀ : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k →* GA D S.B.V
  gl₁ : GL (n₁ ⊕ Fin (c + 1 + 1)) k →* GA D S.J.W
  gl₂ : GL (n₂ ⊕ Fin (c + 1)) k →* GA D S.B'.V
  loc₀ : ∀ g, (ofSplit q).IsLoc F.G₀ (gl₀ g) g
  loc₁ : ∀ g, (ofSplit q).IsLoc F.G₁ (gl₁ g) g
  loc₂ : ∀ g, (ofSplit q).IsLoc F.G₂ (gl₂ g) g
  μ₁ : kˣ →* ℂˣ
  μ₂ : kˣ →* ℂˣ
  comp₁ : (ofSplit q).IsComp S.χ₁⁻¹ μ₁
  comp₂ : (ofSplit q).IsComp S.χ₂⁻¹ μ₂
  open₁ : IsOpen (μ₁.ker : Set kˣ)
  open₂ : IsOpen (μ₂.ker : Set kˣ)
  L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k)
  L₁ : Level (GL (n₁ ⊕ Fin (c + 1 + 1)) k)
  L₂ : Level (GL (n₂ ⊕ Fin (c + 1)) k)
  co₁ : IsCO L₁.J
  co₂ : IsCO L₂.J
  le₁ : L₁.J ≤ KO k _
  le₂ : L₂.J ≤ KO k _
  Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1 + 1)) (n₀ ⊕ Fin (c + 1 + 1 + 1)) k)
  Φ₂ : SB (Matrix (n₂ ⊕ Fin (c + 1)) (n₁ ⊕ Fin (c + 1 + 1)) k)
  ty₁ : HasTypes μ₁ L₀ L₁ Φ₁.1
  ty₂ : HasTypes μ₂ L₁ L₂ Φ₂.1
  D₁ : WO S.B.V S.J.W →₀ ℂ
  D₂ : WO S.J.W S.B'.V →₀ ℂ
  dat₁ : (ofSplit q).IsCombAt ψ F.G₀ F.G₁ D₁ Φ₁.1
  dat₂ : (ofSplit q).IsCombAt ψ F.G₁ F.G₂ D₂ Φ₂.1

  α : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k
  A₁ : Finset (GL (n₁ ⊕ Fin (c + 1 + 1)) k)
  A₂ : Finset (GL (n₂ ⊕ Fin (c + 1)) k)
  cov₁ : Covers 1 L₁.J A₁ fun h => GlobalTheory.StepData.flat ψk ν μ₁ Φ₁.1 α h
  cov₂ : ∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψk ν μ₂ Φ₂.1 γ h
  d₁ : A₁ → WO S.B.A S.J.W₀ →₀ ℂ
  d₂ : A₁ → A₂ → WO S.J.W₀ S.B'.A →₀ ℂ
  ent₁ : ∀ γ, (ofSplit q).IsCombAt ψ F.F₀ F.F₁ (d₁ γ) (xi ψk ν μ₁ Φ₁.1 L₁.J 1 α γ.1)
  ent₂ : ∀ γ β, (ofSplit q).IsCombAt ψ F.F₁ F.F₂ (d₂ γ β) (xi ψk ν μ₂ Φ₂.1 L₂.J 1 γ.1 β.1)
  e₀ : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k →₀ ℂ
  e₂ : A₂ → GL (n₂ ⊕ Fin (c + 1)) k →₀ ℂ
  one₀ : IsOneComb ψk ν (σ + 1 + 1) L₀ α e₀
  one₂ : ∀ β, IsOneComb ψk ν (σ + 1) L₂ β.1 (e₂ β)
  m₁ : Measure (GL n₁ k)
  m₂ : Measure (GL n₂ k)
  haar₁ : m₁.IsHaarMeasure
  haar₂ : m₂.IsHaarMeasure
  vol₁ : m₁ (KO k n₁) = 1
  vol₂ : m₂ (KO k n₂) = 1

attribute [instance] QStep.fld QStep.val QStep.top QStep.loc QStep.mea QStep.bor QStep.f₀ QStep.e₀' QStep.f₁ QStep.e₁' QStep.f₂ QStep.e₂'

namespace QStep
variable {S : Dbl2 ψ σ} (Q : QStep S)

def w₁ (γ : Q.A₁) : ℂ := (((Q.m₁ (prX (Cgrp Q.L₁.J γ.1))).toReal⁻¹ : ℝ) : ℂ)

def w₂ (β : Q.A₂) : ℂ := (((Q.m₂ (prX (Cgrp Q.L₂.J β.1))).toReal⁻¹ : ℝ) : ℂ)

def volJ : ℂ := ((Q.L₁.J.relIndex (KO Q.k _) : ℂ) * (Q.L₂.J.relIndex (KO Q.k _) : ℂ))⁻¹

def Vac (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) : Prop :=
  (∃ T O, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T ∧ IsOne O ∧ T O = f₁) ∧
    ∃ T O, (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T ∧ IsOne O ∧ T O = f₂

def Away {A T : HSp D} (c : WO A T →₀ ℂ) : Prop := ∀ u ∈ c.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u

def Typed (f : GA D S.B'.V → ℂ) : Prop :=
  ∀ j : Q.L₂.J, rTrans (Q.gl₂ j.1) f = (Q.L₂.lam j : ℂ) • f

end QStep

def IntAt {V : HSp D} {k Y : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype Y]
    [DecidableEq Y] (v : GlobalTheory.FinPl.Pl D) (gl : GL Y k →* GA D V) (x : GA D V) : Prop :=
  ∃ κ ∈ KO k Y, x * (gl κ)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = v)

def ValOne (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (G₁ : Measure (GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)) (G₂ : Measure (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)),
    G₁.IsHaarMeasure → G₂.IsHaarMeasure → G₁ (KO Q.k (Q.n₁ ⊕ Fin (Q.c + 1 + 1))) = 1 → G₂ (KO Q.k (Q.n₂ ⊕ Fin (Q.c + 1))) = 1 →
  ∀ c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f →
  ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v),
    ∃ u : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ,
      (∀ x, IsQuotInt Q.ν Q.m₂ G₂ (σ + 1) (fun y => GlobalTheory.PosOne.comb Q.e₀ fun a =>
        S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y)) (u x)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ Q.ν Q.m₁ G₁ (σ + 1) u
        (Q.volJ * ∑ γ : Q.A₁, ∑ β : Q.A₂, Q.w₁ γ * Q.w₂ β *
          S.val (aconv [c₁, Q.d₁ γ]) (aconv [c₂, Q.d₂ γ β]) f₁ f₂ φ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) g h₁ h₂)

def ValQ (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ v, P v ↔ ∃ i, (Q i).q.v = v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W P)) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W P)))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V P)) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V P))),
    μ₁.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₂.IsHaarMeasure → ρ₂.IsHaarMeasure →
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 → ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 →
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 → ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1 →
  ∀ c₁ c₂, (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → (∀ i, (Q i).Vac f₁ f₂) →
  ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → (∀ i, (Q i).Typed f) →
  ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V P, ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W P, ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V P,
    Iter2 ρ₁ μ₁ ρ₂ μ₂
      (fun x y => GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
        S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
          φ f (g * a) (h₁ * x.1) (h₂ * y.1))
      ((∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
        S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
          (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂)

def FinOne (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k),
    ∃ T₁ : Finset (GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k),
      (∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ x,
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) ≠ 0 →
          ∃ t ∈ T₁, ∃ r, Q.gl₁ r ∈ jacGrp S.J.d ∧ ∃ j ∈ Q.L₁.J, x = r * t * j) ∧
      ∀ x, ∃ T₂ : Finset (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v),
        ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ y,
          S.con (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) ≠ 0 →
            ∃ t ∈ T₂, ∃ r, Q.gl₂ r ∈ besGrp S.B'.d S.B'.o ∧ ∃ j ∈ Q.L₂.J, y = r * t * j

end GlobalTheory.QPl
end
