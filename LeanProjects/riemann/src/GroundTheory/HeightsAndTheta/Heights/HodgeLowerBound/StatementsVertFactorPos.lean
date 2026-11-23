import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def VertFactorPos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ),
    p ∈ D.S → ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z

namespace Line

def lineDataVert : ComponentData zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  { lineDataZero with
    S := {2}
    S_prime := fun p hp => by rw [Finset.mem_singleton.1 hp]; exact Nat.prime_two
    vdeg := fun _ => 0
    vnum := fun p => C (p : ℤ)
    vden := fun _ => 1
    vertical := fun p hp => isVerticalDivisorAt_line (by rw [Finset.mem_singleton.1 hp]; norm_num) }

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
