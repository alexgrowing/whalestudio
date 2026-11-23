import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries

section Defs
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A]

def omS {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) : SB (Matrix b a k) :=
  ⟨om μ g h Φ.1, SplitWeil.Model.om_mem_SB μ g h Φ.2⟩

def IsEquivTheta (μ : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) P') (π : Representation ℂ (GL n k) P)
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (φ : P') (Ψ : SB (Matrix n n' k)), θ (π' g φ) (omS μ g h Ψ) = π h (θ φ Ψ)

def HasVecType {G : Type*} [Group G] (σ : Representation ℂ G A) (J : Subgroup G) (lam : J →* ℂˣ) (F : A) : Prop :=
  ∀ κ : J, σ (κ : G) F = (lam κ : ℂ) • F

def HasTargetType {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (J : Subgroup (GL b k)) (lam : J →* ℂˣ) (Φ : Matrix b a k → ℂ) : Prop :=
  ∀ κ : J, om μ 1 (κ : GL b k) Φ = (((lam κ)⁻¹ : ℂˣ) : ℂ) • Φ

variable [MeasurableSpace k] [BorelSpace k]

def flatS (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (h : GL (n ⊕ Fin c) k) : SB (Matrix n n' k) :=
  ⟨flat ψ ν μ Φ.1 1 h, opE_mem_SB 1 ψ ν (SplitWeil.Model.om_mem_SB μ 1 h Φ.2)⟩

def xiOneS (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (J : Subgroup (GL (n ⊕ Fin c) k)) (bas : GL (n ⊕ Fin c) k) :
    SB (Matrix n n' k) :=
  ⟨xi ψ ν μ Φ.1 J bas 1 1,
    (SB (Matrix n n' k)).smul_mem (((volNat ν bas (Cgrp J 1))⁻¹ : ℝ) : ℂ) (flatS ψ ν μ Φ 1).2⟩

def OneCoset (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (J : Subgroup (GL (n ⊕ Fin c) k)) : Prop :=
  idxAt ψ ν μ Φ J 1 ⊆ {DoubleCoset.mk (R k n c 1) J 1}

def integrand (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (φ : P') (F : A) :
    GL (n ⊕ Fin c) k → ℂ := fun h => b (θ φ (flatS ψ ν μ Φ h)) (σ h F)

omit [BorelSpace k] in

theorem oneCoset_iff (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    OneCoset ψ ν μ Φ J ↔ ∀ h, flat ψ ν μ Φ 1 h ≠ 0 → ∃ r ∈ R k n c 1, ∃ κ ∈ J, h = r * κ := by
  constructor
  · intro H h hh
    have h1 : DoubleCoset.mk (R k n c 1) J h = DoubleCoset.mk (R k n c 1) J 1 := H ⟨h, rfl, hh⟩
    obtain ⟨r, hr, κ, hκ, e⟩ := (DoubleCoset.eq _ _ _ _).1 h1.symm
    exact ⟨r, hr, κ, hκ, by simpa using e⟩
  · rintro H _ ⟨h, rfl, hh⟩
    obtain ⟨r, hr, κ, hκ, e⟩ := H h hh
    exact ((DoubleCoset.eq _ _ _ _).2 ⟨r, hr, κ, hκ, by simpa using e⟩).symm

end Defs

section Statement
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def CollapsesWith (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (bas : GL (n ⊕ Fin c) k) (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ)
    (lam : J →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (κ : ℝ) : Prop :=
  ∀ (P' P A : Type) [AddCommGroup P'] [Module ℂ P'] [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
    (π' : Representation ℂ (GL n' k) P') (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A),
    IsSmoothRep π' → IsSmoothRep π → IsSmoothRep σ →
    ∀ (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsPos ψ 1 π σ b →
    ∀ (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P), IsEquivTheta μ π' π θ →
    ∀ (φ : P') (F : A), HasVecType σ J lam F →
    ∀ z : ℂ, IsQuotInt ν μX μG 1 (integrand ψ ν μ Φ σ b θ φ F) z ↔
      z = (κ : ℂ) * b (θ φ (xiOneS ψ ν μ Φ J bas)) F

end Statement

def Collapse : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
    ∀ (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)),
    ν.IsAddHaarMeasure → μX.IsHaarMeasure → μG.IsHaarMeasure →
    ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
      IsCompact (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (bas : GL (n ⊕ Fin c) k),
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
      ∀ (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
        HasTargetType μ J lam Φ.1 → OneCoset ψ ν μ Φ.1 J →
        CollapsesWith ν μX μG J bas ψ μ lam Φ κ

def CollapseWeak : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
    ∀ (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)),
    ν.IsAddHaarMeasure → μX.IsHaarMeasure → μG.IsHaarMeasure →
    ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
      IsCompact (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (bas : GL (n ⊕ Fin c) k) (n' : Type) [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle),
      Continuous ψ → ψ ≠ 1 →
      ∀ (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
        HasTargetType μ J lam Φ.1 → OneCoset ψ ν μ Φ.1 J →
        ∃ κ : ℝ, 0 < κ ∧ CollapsesWith ν μX μG J bas ψ μ lam Φ κ

theorem Collapse.weak (H : Collapse) : CollapseWeak := by
  intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas n' _ _ ψ hψ hψ1 μ lam Φ h1 h2
  obtain ⟨κ, hκ, H'⟩ := H k n c hc ν μX μG hν hX hG J ho hcp bas
  exact ⟨κ, hκ, H' n' ψ hψ hψ1 μ lam Φ h1 h2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
