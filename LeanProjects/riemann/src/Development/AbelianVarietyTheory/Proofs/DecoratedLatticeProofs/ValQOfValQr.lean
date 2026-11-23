import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QVal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def places {r : ℕ} (Q : Fin r → QStep S) : GlobalTheory.FinPl.Pl D → Prop := fun v => ∃ i, (Q i).q.v = v

def integrand {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
    S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
      φ f (g * a) (h₁ * x) (h₂ * y)

def value {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : ℂ :=
  (∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
    S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
      (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂

def innerVal {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, ((Q 0).w₁ γ * (Q 0).w₂ β) *
    integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ x y

def Hyps {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : Prop :=
  (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ (∀ i, (Q i).Vac f₁ f₂) ∧
    IsContAut S.B.A φ ∧ IsContAut S.B'.V f ∧ (∀ i, (Q i).Typed f) ∧ g ∈ GlobalTheory.FinPl.grpOff S.B.V (places Q) ∧
    h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (places Q) ∧ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (places Q)

def Norm {r : ℕ} (Q : Fin r → QStep S) (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q)))
    (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q)))) (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))) : Prop :=
  μ₁.IsHaarMeasure ∧ ρ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ ρ₂.IsHaarMeasure ∧
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 ∧ ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 ∧
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 ∧ ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1

def LocNorm (Q₀ : QStep S) (m₁ : Measure (GL (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1)) Q₀.k)) (s₁ : Measure (RFJ Q₀.k Q₀.n₁ (Q₀.c + 1 + 1) (σ + 1)))
    (m₂ : Measure (GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)) (s₂ : Measure (R Q₀.k Q₀.n₂ (Q₀.c + 1) (σ + 1))) : Prop :=
  m₁.IsHaarMeasure ∧ m₁ (KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))) = 1 ∧ s₁.IsHaarMeasure ∧
    s₁ {x | x.1 ∈ KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))} = 1 ∧ m₂.IsHaarMeasure ∧ m₂ (KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))) = 1 ∧
    s₂.IsHaarMeasure ∧ s₂ {x | x.1 ∈ KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))} = 1

def levJ {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.J.W (places Q)) :=
  (⨆ i, (Q i).L₁.J.map (Q i).gl₁).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))

def levB {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) :=
  (⨆ i, (Q i).L₂.J.map (Q i).gl₂).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q))

end GlobalTheory.QVal

namespace GlobalTheory.QVal

def ValQr (D : D7) (r : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ →
  ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ →
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)

theorem valQ_of_valQr (D : D7) (h : ∀ r, ValQr D r) : ValQ D := by
  intro ψ hψ σ S r Q hinj P hP μ₁ ρ₁ μ₂ ρ₂ a1 a2 a3 a4 a5 a6 a7 a8 c₁ c₂ hc f₁ f₂ t1 t2 hv φ f hφ hf ht g hg h₁ hh₁ h₂ hh₂
  have e : P = places Q := funext fun v => propext (hP v)
  subst e
  exact h r ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ c₁ c₂ f₁ f₂ φ f g h₁ h₂
    ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩

end GlobalTheory.QVal

namespace GlobalTheory.QVal
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def pint {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V)
    (x : GlobalTheory.FinPl.grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)
    (y : GlobalTheory.FinPl.grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) : ℂ :=
  integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)
end GlobalTheory.QVal

end
