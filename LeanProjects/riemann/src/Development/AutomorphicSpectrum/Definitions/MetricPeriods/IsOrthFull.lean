import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.HeightsSetAll

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt

variable {K : Type} [Field K] [NumberField K]

def sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ((E.metric.form σ).inner x x).re

def OrthAt (E : HermitianBundle.{0} K) (F F' : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ), ∀ x ∈ F, ∀ y ∈ F',
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] y) = 0

structure SatFlag (E : HermitianBundle.{0} K) (r : ℕ) where

  F : Fin (r + 1) → Submodule (𝓞 K) E.carrier
  mono : Monotone F
  sat : ∀ i, E.Saturated (F i)
  rank : ∀ i, E.rank (F i) = i

namespace SatFlag

variable {E : HermitianBundle.{0} K} {r : ℕ}

def top (A : SatFlag E r) : Submodule (𝓞 K) E.carrier := A.F (Fin.last r)

def grDeg (A : SatFlag E r) (i : Fin r) : ℝ := E.normDegree (A.F i.succ) - E.normDegree (A.F i.castSucc)

end SatFlag

structure FlagPair (E : HermitianBundle.{0} K) (Ψ : Type) (j k : ℕ) where

  W : Ψ → SatFlag E j

  S : Ψ → SatFlag E k

namespace FlagPair

variable {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {j k : ℕ}

def lamDeg (A : FlagPair E Ψ j k) (lam : Ψ → Fin (j + k) → ℝ) : ℝ :=
  ∑ τ, (-(∑ i : Fin j, lam τ (Fin.castAdd k i) * (A.W τ).grDeg i) +
    ∑ i : Fin k, lam τ (Fin.natAdd j i) * (A.S τ).grDeg i.rev)

def flatDeg (A : FlagPair E Ψ j k) (τ : Ψ) : ℝ := E.normDegree (A.W τ).top - E.normDegree (A.S τ).top

def part (A : FlagPair E Ψ j k) : Ψ ⊕ Ψ → Submodule (𝓞 K) E.carrier :=
  Sum.elim (fun τ => (A.W τ).top) (fun τ => (A.S τ).top)

def IsOrthFull (A : FlagPair E Ψ j k) : Prop :=
  (∀ a b, a ≠ b → OrthAt E (A.part a) (A.part b)) ∧ Fintype.card Ψ * (j + k) = Module.finrank (𝓞 K) E.carrier

end FlagPair

end GlobalTheory.CompanionTheory.Ar
