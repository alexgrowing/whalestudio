import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.DFrameBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  P.FromX → P.Base i0 i0' → ∀ γ h h' : X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' γ h h' → ∀ v,
    Formalism.FourierDecayAlt.D.IsDFrame (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v))
      (trG (P.Q v) (P.Qi v) ((h⁻¹ * γ * h') v))

end Formalism.L2.SG.Pf.Carrier
