import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA := {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def nearNe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | IsNear B d (epN B) x γ ∧ γ ≠ 1}

def nearAbs (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : nearNe B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def nearBound (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) * mainTerm B d

def NearModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, nearAbs B d x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (nearBound B d)

theorem nearAbs_eq_zero (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (h : ∀ γ, IsNear B d (epN B) x γ → γ = 1) : nearAbs B d x = 0 := by
  haveI : IsEmpty (nearNe B d x) := ⟨fun γ => γ.2.2 (h γ.1 γ.2.1)⟩
  simp [nearAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms
