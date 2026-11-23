import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def SplitPt.IsIdele {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (x : kˣ) (a : (AE D)ˣ) : Prop := (a : AE D) = p.sec x + (1 - p.e)

def chrPow (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : ℂ := ((χ a ^ e : Circle) : ℂ)

def LiftExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1), ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D),
    CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n),
    ∀ a, p.IsIdele q.unit a → ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f →
    ∀ φ₀, RamAt α P φ₀ → ∀ ε : 𝓀[k]ˣ,
      sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) =
        ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * chrPow χS a e * chrPow χT a (-e)) •
          liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f

def RamUnitary (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (S : HSp D),
    CoCpt S → ∀ (vS : Vol S) (β : Frame p S n) (P : Pair k n) (φ φ' : GA D S → ℂ), RamAt β P φ → RamAt β P φ' →
      ∫ g in vS.𝓕, sOp β P q (resChar χ hχ q) ε φ g * star (sOp β P q (resChar χ hχ q) ε φ' g) ∂vS.μ =
        (resCard k : ℂ) ^ Fintype.card n * ∫ g in vS.𝓕, φ g * star (φ' g) ∂vS.μ

def DoubleCollapse (D : D7) : Prop :=
  ∀ (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (Λ : DblLat B J B') (P : Pl D → Prop),
    IsSelfDualC J.W Λ.L₁ → IsSelfDualC B'.V Λ.L₂ →
    ∀ (μ₁ : Measure (GA D J.W)) (μ₂ : Measure (GA D B'.V)) (m₁ : Measure (grpOff J.W P))
      (ν₁ : Measure ((jacGrp J.d).subgroupOf (grpOff J.W P))) (m₂ : Measure (grpOff B'.V P))
      (ν₂ : Measure ((besGrp B'.d B'.o).subgroupOf (grpOff B'.V P))),
      μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → m₁.IsHaarMeasure → ν₁.IsHaarMeasure → m₂.IsHaarMeasure → ν₂.IsHaarMeasure →
    ∃ c : ℝ, 0 < c ∧
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
      (p : ι → SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
      [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n)
      (a' : PairDat p B'.A B'.V₀ n''), DblShape s₁ s₂ Λ P q a b a' →
      ∀ Φ₁ Φ₂, Vac ψ B.V J.W Λ.L₀ Λ.L₁ P Φ₁ → Vac ψ J.W B'.V Λ.L₁ Λ.L₂ P Φ₂ → ∀ g ∈ grpOff B.V P, ∀ φ, a.Ram φ →
      ∀ G : GA D B'.V → ℂ, (∀ κ, InK B'.V Λ.L₂ P κ → rTrans κ G = G) → ∀ (f₁ : GA D J.W → ℂ) (z : ℂ),
        IsQuotIntL1 J.μR μ₁ f₁ z →
        (∀ h₁, IsQuotIntL1 B'.μR μ₂ (fun h₂ => B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)) (f₁ h₁)) →
        ∃ (f₁' : grpOff J.W P → ℂ) (z' : ℂ), IsQuotIntL1 ν₁ m₁ f₁' z' ∧ z = c * z' ∧
          ∀ h₁ : grpOff J.W P, IsQuotIntL1 ν₂ m₂
            (fun h₂ : grpOff B'.V P => B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans (h₂ : GA D B'.V) G)) (f₁' h₁)

end GlobalTheory.FinPl

end
