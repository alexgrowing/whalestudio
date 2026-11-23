import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  first | exact @GlobalTheory.FockTaylor.hasSum_derivAt0 | exact GlobalTheory.FockTaylor.hasSum_derivAt0 | (intros; apply GlobalTheory.FockTaylor.hasSum_derivAt0 <;> assumption)
