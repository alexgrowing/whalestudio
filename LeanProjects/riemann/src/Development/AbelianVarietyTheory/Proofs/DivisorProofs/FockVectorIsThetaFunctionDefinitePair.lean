import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ThetaFinsetSum

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem fock_isThetaFunO : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  intro D cc δ t0 Q P X hX T
  exact Formalism.IndefR.Fin.ptStable D X.ψ X.θ hX.2.weil.std hX.2.inf X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) X.vac _ hX.2.vac_theta

end GlobalTheory.NormDict
