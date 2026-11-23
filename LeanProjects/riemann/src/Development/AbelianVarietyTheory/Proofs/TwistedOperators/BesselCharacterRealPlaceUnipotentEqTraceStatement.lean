import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTrace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_realPlace_unipotent_eq_trace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  first | exact @GlobalTheory.BesselCoords.besChar_atTau_coords | exact GlobalTheory.BesselCoords.besChar_atTau_coords | (intros; apply GlobalTheory.BesselCoords.besChar_atTau_coords <;> assumption)
