import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

theorem joint_tensor_factorization (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u') (hLU : LocUni X u u')
    (hGP : GlobProd X u u')
    (hPJ : ∀ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ w, OkPt X u u' w → LocPin X u u' w νl) → PlaceJ P sc i0 i0' νl) :
    P.JointTensor sc i0 i0' νq := by
  obtain ⟨νl, hpin, hQ⟩ := ooQuot_pin X u u' νq hN hR hLU hGP
  exact jointTensor_of_steps P sc i0 i0' νq νl hQ (hPJ νl hpin)

end Formalism.L2.SG.Pf.Carrier.JointFinal
