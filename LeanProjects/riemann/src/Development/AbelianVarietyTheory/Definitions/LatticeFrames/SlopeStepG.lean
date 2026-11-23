import Mathlib
import Formalism.LocalRingCardinality.DataArith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep

noncomputable section

namespace GlobalTheory.Core

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def MuMaxLe (B : HLat K) (c : ℝ) : Prop := 0 < B.rank → B.muMax ≤ c

def Into (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) : Prop := ∀ x ∈ N.L, Ψ x ∈ B.L

def HtLe (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) (h : ℝ) : Prop :=
  Ψ ≠ 0 → Formalism.HN.htMap N.b N.X B.b B.X Ψ ≤ h

def RkHalf (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) : Prop :=
  Module.finrank K N.V < 2 * Module.finrank K (LinearMap.range Ψ)

def InPow {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (A : Submodule (𝓞 K) V) (x : V) : Prop :=
  ∀ a : K, (a = 0 ∨ -n ≤ vAdd w a) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (a • x) ∈ A

def SlopeStepG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (N B : HLat K)
    (Ψ : N.V →ₗ[K] B.V) (h c : ℝ), N.Good → B.Good →
    MuMaxLe B c → Into N B Ψ → HtLe N B Ψ h → RkHalf N B Ψ → SlopeLe N (h + c)

end GlobalTheory.Core

end
