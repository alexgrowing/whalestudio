import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntegralCompWeil
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.QuadraticOperatorPureTensor

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def OpCLM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
        (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

def AwayFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), g = x * ι y ∧ ∀ Ψ, AwayCls θ τ fr Ψ → ∃ Ψ', AwayCls θ τ fr Ψ' ∧
      ∀ (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ) (hS : tens θ τ fr S Ψ ∈ schwartzA θ V.rank n),
        (ω x ⟨tens θ τ fr S Ψ, hS⟩).1 = tens θ τ fr S Ψ'

def SchDeriv : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n),
    ∃ (S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ) (S' : SchwartzMap (Fin m → Fin n → ℂ) ℂ),
      (∀ t y, S t y = fP c P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin m) (Fin m) ℂ) * (Matrix.of y : Matrix (Fin m) (Fin n) ℂ))) ∧
      (∀ y, S' y = fP c (vfX c X P) y) ∧
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (S t - S 0)) (nhdsWithin 0 {0}ᶜ) (nhds S')

end PositivityTheory.Rg.Sw.Glob
