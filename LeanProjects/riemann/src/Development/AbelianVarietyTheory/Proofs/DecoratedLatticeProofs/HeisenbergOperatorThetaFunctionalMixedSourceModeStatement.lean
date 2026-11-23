import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = d.mixS T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • d.mixS T ψ v.μ v.𝓕 f x) ∧ (∀ x w, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w (d.mixS T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => d.mixS T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  first | exact @GlobalTheory.HeisMixSource.heis_mixS | exact GlobalTheory.HeisMixSource.heis_mixS | (intros; apply GlobalTheory.HeisMixSource.heis_mixS <;> assumption)
