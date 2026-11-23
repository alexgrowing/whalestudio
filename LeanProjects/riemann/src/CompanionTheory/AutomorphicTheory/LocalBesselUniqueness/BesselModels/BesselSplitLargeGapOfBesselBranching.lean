import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit

noncomputable section

namespace CompanionTheory.Lime.BM

open Formalism.L2.SG.BesselSplit

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory Finset
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselSplitLargeGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    1 ≤ k → Formalism.QuantumDeterminants.GapAtLeast ε lam h → 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∃ B : H → Vp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
    ∃ v ∈ smoothVecs (k := k) (r := r) σ, ∃ v' ∈ smoothVecs (k := k) (r := r) σ,
      beOp μW μN σ π (psiGen k r z c) v v' ≠ 0

end CompanionTheory.Lime.BM
