import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top Filter Topology

def SmallOnTower : Prop :=
  VolumeInputs →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ)
    (u : Wt Ψ N) (g Λ cs cc ρ : ℝ) (G : ∀ c, GenModel (T.M B c) Λ),
    IsFullIntersectionSystem II → 1 ≤ dimFl Ψ N → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 →
    Real.log Λ ≤ cs → 0 ≤ cc → (∀ c, (1 - ρ) * (G c).del ≤ T.vol c * flagDeg u) →
    (∀ c, (G c).HasInputs (T.lamS u) cc) →
    ((∀ c, 0 ≤ (G c).ht II + cs) ∧ 0 ≤ cc ∧
      ∀ c, (1 - ρ) * max 0 (T.slope II B c u + cs) ≤ (G c).ht II + cs + cc) ∧
    ∀ c, T.vol c * flagDeg u ≤ (G c).del

end GlobalTheory.CompanionTheory.Ar.Small
