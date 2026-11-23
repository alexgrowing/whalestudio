import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_contraction_integrand_continuous_periodic : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  first | exact @GlobalTheory.ContrComb.integrand_cont_per | exact GlobalTheory.ContrComb.integrand_cont_per | (intros; apply GlobalTheory.ContrComb.integrand_cont_per <;> assumption)
