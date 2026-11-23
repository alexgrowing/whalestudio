import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilKernelFunctional_superposition_isTame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T), Measurable c → Continuous g → Continuous h → Continuous w → (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) → (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧ Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  first | exact @GlobalTheory.KerTame.kernel_tame | exact GlobalTheory.KerTame.kernel_tame | (intros; apply GlobalTheory.KerTame.kernel_tame <;> assumption)
