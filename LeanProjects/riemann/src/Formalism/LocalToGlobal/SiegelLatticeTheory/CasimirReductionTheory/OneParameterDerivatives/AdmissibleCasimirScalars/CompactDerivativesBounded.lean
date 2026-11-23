import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def isoK (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Submodule ℂ H :=
  eqImg (fun k : KG ε => σ (toMK k)) S

def dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def sg (ε : Fin n → Bool) (p : Fin n × Fin n) : ℝ := if ε p.1 = ε p.2 then 1 else -1

def wt (p : Fin n × Fin n) : ℝ := if p.1 = p.2 then 1 else 1 / 2

def gen (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  if p.1 = p.2 then Complex.I • Matrix.single p.1 p.1 (1 : ℂ)
  else if p.1 < p.2 then Matrix.single p.1 p.2 (1 : ℂ) - (sg ε p : ℂ) • Matrix.single p.2 p.1 (1 : ℂ)
  else Complex.I • (Matrix.single p.2 p.1 (1 : ℂ) + (sg ε p : ℂ) • Matrix.single p.1 p.2 (1 : ℂ))

def Cas (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : H :=
  - ∑ p : Fin n × Fin n, ((wt p * sg ε p : ℝ) : ℂ) • dS σ (gen ε p) (dS σ (gen ε p) v)

structure Calc (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) : Prop where

  der : ∀ X, inG ε X → ∀ v ∈ D, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dS σ X v) 0

  mem : ∀ X, inG ε X → ∀ v ∈ D, dS σ X v ∈ D

  lin : ∀ (z : Fin n × Fin n → ℝ), ∀ v ∈ D,
    dS σ (∑ p, ((z p : ℝ) : ℂ) • gen ε p) v = ∑ p, ((z p : ℝ) : ℂ) • dS σ (gen ε p) v

  skew : ∀ X, inG ε X → ∀ u ∈ D, ∀ v ∈ D, ⟪dS σ X u, v⟫_ℂ = - ⟪u, dS σ X v⟫_ℂ

  conj : ∀ (g : UJ ε) X, inG ε X → ∀ v ∈ D, σ (umat g) (dS σ X v) = dS σ (umat g * X * umat g⁻¹) (σ (umat g) v)

  mv : ∀ X, inG ε X → ∀ v ∈ D, ‖σ (NormedSpace.exp X) v - v‖ ≤ ‖dS σ X v‖

end Defs

def SmoothVectorsDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), IsIrredOn (UJset ε) σ → ∀ w : H, w ≠ 0 →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      ∀ v ∈ isoK ε σ S, v ∈ closure ((Vsub ε hσ w ⊓ isoK ε σ S : Submodule ℂ H) : Set H)

def CalculusOnSmoothVectors : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ) (w : H), Calc ε σ (Vsub ε hσ w)

def CasimirProperties : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H), Calc ε σ D →
    (∀ (g : UJ ε), ∀ v ∈ D, σ (umat g) v ∈ D) →
      (∀ u ∈ D, ∀ v ∈ D, Cas ε σ (u + v) = Cas ε σ u + Cas ε σ v) ∧
      (∀ (c : ℂ), ∀ v ∈ D, Cas ε σ (c • v) = c • Cas ε σ v) ∧
      (∀ u ∈ D, ∀ v ∈ D, ⟪Cas ε σ u, v⟫_ℂ = ⟪u, Cas ε σ v⟫_ℂ) ∧
      (∀ (g : UJ ε), ∀ v ∈ D, Cas ε σ (σ (umat g) v) = σ (umat g) (Cas ε σ v))

def SchurSymmetricDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ D : Submodule ℂ H, D.topologicalClosure = ⊤ → (∀ (g : UJ ε), ∀ v ∈ D, σ (umat g) v ∈ D) →
    ∀ T : H → H, (∀ u ∈ D, ∀ v ∈ D, T (u + v) = T u + T v) → (∀ (c : ℂ), ∀ v ∈ D, T (c • v) = c • T v) →
      (∀ u ∈ D, ∀ v ∈ D, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ) → (∀ (g : UJ ε), ∀ v ∈ D, T (σ (umat g) v) = σ (umat g) (T v)) →
      ∃ c : ℝ, ∀ v ∈ D, T v = (c : ℂ) • v

def CasScalarStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), IsIrredOn (UJset ε) σ → ∀ w : H, w ≠ 0 →
      ∃ c : ℝ, ∀ v ∈ Vsub ε hσ w, Cas ε σ v = (c : ℂ) • v

def CasimirScalarBounded : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H), Calc ε σ D →
    ∀ c : ℝ, (∀ v ∈ D, Cas ε σ v = (c : ℂ) • v) → ∀ (W : Submodule ℂ H) (C : ℝ),
      (∀ p : Fin n × Fin n, ε p.1 = ε p.2 → ∀ v ∈ W, ‖dS σ (gen ε p) v‖ ≤ C * ‖v‖) →
      ∃ C' : ℝ, ∀ p : Fin n × Fin n, ∀ v ∈ D, v ∈ W → ‖dS σ (gen ε p) v‖ ≤ C' * ‖v‖

def CompactDerivativesBounded : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      ∃ C : ℝ, ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → ∀ v ∈ isoK ε σ S, ‖dS σ (gen ε p) v‖ ≤ C * ‖v‖

def SmallMotionNeighbourhood : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H), Calc ε σ D →
    ∀ (W : Submodule ℂ H) (C' : ℝ), (∀ p : Fin n × Fin n, ∀ v ∈ D, v ∈ W → ‖dS σ (gen ε p) v‖ ≤ C' * ‖v‖) →
      (∀ v ∈ W, v ∈ closure ((D ⊓ W : Submodule ℂ H) : Set H)) →
      ∃ U ∈ 𝓝 (1 : UJ ε), ∀ g ∈ U, ∀ v ∈ W, ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2

def FormalDegreeFiniteDim : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ d : ℝ, IsFdeg (muG ε) σ d →
    ∀ (W : Submodule ℂ H), ∀ U ∈ 𝓝 (1 : UJ ε), (∀ g ∈ U, ∀ v ∈ W, ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2) →
      FiniteDimensional ℂ W

end Formalism.L2.SG.Pf.admitted
