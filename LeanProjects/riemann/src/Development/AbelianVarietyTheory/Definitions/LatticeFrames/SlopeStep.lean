import Mathlib
import Formalism.LocalRingCardinality.DataArith

noncomputable section

namespace GlobalTheory.Core

open NumberField Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Target (M : HLat K) : Prop := 0 < M.rank → M.muMaxDual ≤ 0

def IntoDual (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : Prop :=
  N.L.map (Φ.restrictScalars (𝓞 K)) ≤ M.dualL

def htPhi (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : ℝ :=
  Formalism.HN.htMap N.b N.X M.dualB M.dualX Φ

def HeightLe (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) (h : ℝ) : Prop :=
  Φ ≠ 0 → htPhi N M Φ ≤ h

def RankHalf (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : Prop :=
  Module.finrank K N.V < 2 * Module.finrank K (LinearMap.range Φ)

def SlopeLe (N : HLat K) (h : ℝ) : Prop := 2 * N.mu - N.muMax ≤ h

def SlopeStep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (N M : HLat K)
    (Φ : N.V →ₗ[K] Module.Dual K M.V) (h : ℝ), N.Good → M.Good →
    Target M → IntoDual N M Φ → HeightLe N M Φ h → RankHalf N M Φ → SlopeLe N h

end GlobalTheory.Core

end
