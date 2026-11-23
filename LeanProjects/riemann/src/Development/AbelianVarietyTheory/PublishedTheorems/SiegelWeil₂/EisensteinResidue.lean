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

def EisensteinResidue : Prop :=
  ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ r), IsAniso V₀ → 0 < r →
  ∀ (l : Lvl V) (l₀ : Lvl V₀), l.Good → l₀.Good → Compat d l l₀ → HasIw d l.K →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ h, PoleLE (sphericalEisensteinSeriesOnGroup d l.K h) (rhoH V r) 1 ∧ ResidueAt (sphericalEisensteinSeriesOnGroup d l.K h) (rhoH V r) κ

end GlobalTheory.Published

end
