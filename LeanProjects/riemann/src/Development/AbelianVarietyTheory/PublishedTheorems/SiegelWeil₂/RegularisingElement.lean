import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def RegularisingElement : Prop :=
  ∀ (D : D7) (n : ℕ) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ r), IsAniso V₀ → 0 < r → V.rank ≤ n →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω →
  ∀ (l : Lvl V) (l₀ : Lvl V₀), l.Good → l₀.Good → Compat d l l₀ → HasIw d l.K →
  ∀ τ : D.what₂.Tau, ∃ (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ),
    IsRegS τ ω d l.K zG zH P ∧ P.eval (rhoH V r : ℂ) ≠ 0

end GlobalTheory.Published

end
