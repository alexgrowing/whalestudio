import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

def PropFTop : Prop :=
  PtsIntegrableStatement → MetricLocalStatement → DegreeStatement →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
      (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (rd Lval : ℝ),
      IsIntersectionSystem II → T.Conv II → T.Proportional → T.Prop6 II frob → 1 ≤ rd → (∀ p ∈ T.bad, p.Prime) →
      (∀ c τ, ∃ R : RootFlat (T.M 2 c) τ, NearRecord N T.bad rd Lval R.ht) → T.PropF II 4 rd Lval

end GlobalTheory.CompanionTheory.Ar.Flat
