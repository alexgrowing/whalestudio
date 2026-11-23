import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def ftLoc {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace.re : ℂ))

def FTfact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
    ∃ (κ : ℂ) (A A' : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)), κ ≠ 0 ∧ ∀ Ψ (hΨ : AwayCls θ τ fr Ψ),
      AwayCls θ τ fr (A Ψ) ∧ AwayCls θ τ fr (A' Ψ) ∧ ∀ f (hf : IsSch f),
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧ IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) f u) (A Ψ) ∧
        (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ)

def GenA : Prop :=
  ∀ (D : D7) (n : ℕ), Subgroup.closure {g : G D n | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨
    (∃ c, mat g = blk4 1 0 c 1)} = ⊤

def LocalL2Isometry : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ y : GR n, ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2

end PositivityTheory.Rg.Sw.Glob
