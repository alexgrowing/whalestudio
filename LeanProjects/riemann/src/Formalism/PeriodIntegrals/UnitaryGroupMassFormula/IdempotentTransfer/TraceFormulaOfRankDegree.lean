import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

def RankPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ

def DegPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      |degL A (cut A ρ (eps P * eG T) A.L) -
          ∑ s, (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        10 * laG G * (rkT T P0 P A ρ : ℝ)

def MuPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      (0 < rkT T P0 P A ρ →
        muMaxL A (cut A ρ (eps P * eG T) A.L) ≤ muMaxL A (cut A ρ (eps P0 * eG T) A.L) + 10 * laG G)

theorem trace_formula_of_rank_degree (h1 : RankPart) (h2 : DegPart) (h3 : MuPart) : PI.Dv.Conclusion4a := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  exact ⟨h1 K G T P0 P hM A ρ hA, h2 K G T P0 P hM A ρ hA, h3 K G T P0 P hM A ρ hA⟩

end PI.Dv.Tr
