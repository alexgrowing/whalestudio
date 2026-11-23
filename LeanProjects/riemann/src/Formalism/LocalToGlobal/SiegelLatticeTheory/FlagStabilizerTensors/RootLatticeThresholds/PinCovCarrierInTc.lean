import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinCov_carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (Hj : ∀ j : Fin (nfE D),
      ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j)))),
        Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
          (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
          (tauE X e j) γ μRv ν →
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
          Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
          Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
            (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
            (Formalism.L2.SG.Pf.Carrier.CarPinTor.fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (cc j))) :
    Formalism.L2.SG.Pf.Carrier.JointPin.PinCov
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo) := by
  intro v γ μRv ν hH
  obtain ⟨j, rfl⟩ := (tauE X e).surjective v
  have key : ∀ (j' : Fin (nfE D)) (h' : X.pl.symm (e (plE D j')) = tauE X e j),
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
        Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
        ((castLoc X u h').toContinuousLinearEquiv.toContinuousLinearMap :
            X.Vloc u (tauE X e j') →L[ℂ] X.Vloc u (tauE X e j)).comp
          ((Formalism.FourierDecayAlt.D.orbJ (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
              (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
              (fcT X C e u u' a b ξ ξ' cc j')).comp
            ((castLoc X u' h').symm.toContinuousLinearEquiv.toContinuousLinearMap :
              X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u' (tauE X e j'))) := by
    intro j' h'
    have hj : j' = j := (tauE X e).injective h'
    subst hj
    rw [towersOf_base, Hj j' γ μRv ν hH]
    ext x
    rfl
  exact key _ (tauE_symm X e (tauE X e j))

end Formalism.L2.SG.Pf.CarrierT
