import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped ComplexConjugate InnerProductSpace ContDiff

namespace PositivityTheory.RgBcC.Real

open PositivityTheory.RgTw (Mat G th IsThetaOp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def IsLefK (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) : Prop :=
  (∀ k, T * E.ρ k = E.ρ k * T) ∧ T * T = 1 ∧
    ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → (Function.Injective fun a => z a ^ 2) →
      LinearMap.trace ℂ E.V (E.ρ k : E.V →ₗ[ℂ] E.V) = (∏ a, ∏ b, (1 + z a / z b)) * conj (weylChar lam z) ^ 2 ∧
      LinearMap.trace ℂ E.V ((E.ρ k * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        (∏ a, ∏ b, (1 + z a / z b)) * conj (weylChar lam fun a => z a ^ 2)

def CxExK : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∃ E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T ∧ IsLefK lam E T

section

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def uG (k : Matrix.unitaryGroup (Fin n) ℂ) : G n := Unitary.toUnits k

open Classical in

def piM (g : Mat n) : U →L[ℂ] U := if h : IsUnit g then π h.unit else 0

def IsInvT (E : KMod n) (t : (E.V →L[ℂ] ℂ) →L[ℂ] U) : Prop := ∀ k ξ, t (ξ ∘L E.ρ k⁻¹) = π (uG k) (t ξ)

def HasInf (χ : Inf n) : Prop :=
  ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k, ∀ v ∈ S, π (uG k) v ∈ S) → ∀ v ∈ S, ∀ w,
    ContDiffOn ℝ ∞ (fun g => ⟪w, piM π g v⟫_ℂ) (GLs n) ∧ IsEig χ fun g => ⟪w, piM π g v⟫_ℂ

end

def RealTr (reg : Bool) : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → (reg = true → StrictAnti lam) → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U]
      [InnerProductSpace ℂ U] [CompleteSpace U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U), IsUnitaryRep π →
      IsTopIrreducible π → IsThetaOp n π A → A * A = 1 → HasInf π (infOf lam) → (∃ t, IsInvT π E t ∧ t ≠ 0) →
      ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ ∀ k val (T' : ℝ), IsMult μ E k val T' →
        HasTrace (repOp π μ (phiOf E T k) ∘L A) (s * 2 ^ n * val (infOf lam))

end PositivityTheory.RgBcC.Real
