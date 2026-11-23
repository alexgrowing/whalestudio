import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFFCurve

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

def RootLineDeRhamModel : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (j p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (_ : DRTie M j p H), p.Prime → 2 < p → 1 ≤ j → j < N →
    ∀ mu : Wt Ψ N, Dominant mu → NefThreshold j p mu → M.NefAt p mu 0

end GlobalTheory.CompanionTheory.Ar.Conj
