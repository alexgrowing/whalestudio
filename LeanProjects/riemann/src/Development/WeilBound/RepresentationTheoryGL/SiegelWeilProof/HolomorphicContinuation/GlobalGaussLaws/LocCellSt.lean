import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def CompInj : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (x y : Mx D m n), (∀ τ, compAt θ τ x = compAt θ τ y) →
    x.map (finPart D) = y.map (finPart D) → x = y

def WEx : Prop := ∀ (D : D7) (n : ℕ), ∃ W : G D n, mat W = blk4 0 1 (-1) 0

def UnipTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n),
      (ω (ι y) Φ).1 x = Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace) * Φ.1 x

end PositivityTheory.Rg.Sw.Glob
