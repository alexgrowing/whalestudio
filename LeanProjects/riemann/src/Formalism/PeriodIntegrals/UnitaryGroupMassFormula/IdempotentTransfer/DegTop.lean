import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

def SplitBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      |degL A (cut A ρ (eps P * eG T) A.L) - ∑ s, degL A (cut A ρ (eps P * eS T s) A.L)| ≤
        5 * laG G * (rkT T P0 P A ρ : ℝ)

def PerSBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ → ∀ s : T.S,
      |degL A (cut A ρ (eps P * eS T s) A.L) - (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        5 * laG G * ((nS T P s * rS T P0 A ρ s : ℕ) : ℝ)

theorem degPart_of (h1 : SplitBound) (h2 : PerSBound) : DegPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  have hs := h1 K G T P0 P hM A ρ hA
  have hp := h2 K G T P0 P hM A ρ hA
  set a := degL A (cut A ρ (eps P * eG T) A.L)
  set c : T.S → ℝ := fun s => degL A (cut A ρ (eps P * eS T s) A.L)
  set b : T.S → ℝ := fun s => degL A (cut A ρ (eps P0 * eS T s) A.L)
  have hsum : |∑ s, (c s - (nS T P s : ℝ) * b s)| ≤ 5 * laG G * (rkT T P0 P A ρ : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun s _ => hp s).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, rkT]
    push_cast
    rfl
  calc |a - ∑ s, (nS T P s : ℝ) * b s|
      = |(a - ∑ s, c s) + ∑ s, (c s - (nS T P s : ℝ) * b s)| := by
        rw [Finset.sum_sub_distrib]; ring_nf
    _ ≤ |a - ∑ s, c s| + |∑ s, (c s - (nS T P s : ℝ) * b s)| := abs_add_le _ _
    _ ≤ 5 * laG G * (rkT T P0 P A ρ : ℝ) + 5 * laG G * (rkT T P0 P A ρ : ℝ) := add_le_add hs hsum
    _ = 10 * laG G * (rkT T P0 P A ρ : ℝ) := by ring

end PI.Dv.Tr
