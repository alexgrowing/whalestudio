import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralHermitianAdjointCovolOnePeriodicEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hermitianAdjoint_covolOne_periodic_eq : ∀ (D : D7) (V W : HSp D) (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL V W) ν 𝓖' → IsCovolOne (ratL W V) μ 𝓕 → ∀ (Φ : WO V W → ℂ), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W), Φ (ratW W V γ + u) = Φ u) → ∫ y in 𝓖', Φ (GlobalTheory.PairLift.adjO V W y) ∂ν = ∫ u in 𝓕, Φ u ∂μ := by
  first | exact @GlobalTheory.SWChangeVar.integral_adjO_eq | exact GlobalTheory.SWChangeVar.integral_adjO_eq | (intros; apply GlobalTheory.SWChangeVar.integral_adjO_eq <;> assumption)
