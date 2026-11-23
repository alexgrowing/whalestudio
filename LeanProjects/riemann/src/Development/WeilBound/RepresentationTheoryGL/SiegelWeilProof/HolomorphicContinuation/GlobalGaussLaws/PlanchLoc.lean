import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def PlanchLoc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t : ℝ), t ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f →
    ∫ u, ‖ftLoc ε t f u‖ ^ 2 = c * ∫ u, ‖f u‖ ^ 2

def AwayNZ : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0

end PositivityTheory.Rg.Sw.Glob
