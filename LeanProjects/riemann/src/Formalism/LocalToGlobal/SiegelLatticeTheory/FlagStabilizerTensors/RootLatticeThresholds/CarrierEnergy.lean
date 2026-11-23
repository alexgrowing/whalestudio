import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Gam0 (P : Parts X u u') : ℝ :=
  Formalism.FourierDecayAlt.D.GamLev P.S.G.k P.S.G.r (Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E))
    (Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0

def Parts.EnergyModel (P : Parts X u u') : Prop :=
  P.Built → (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace P.S P.T P.f P.χ v (P.L v) (P.j v) (P.lam v) P.c (P.Cm v) (P.σ v)) →
    ∀ v, Formalism.FourierDecayAlt.JCT.jvModel P.S P.j P.Cm v = (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0

def Parts.EnergyNorm (P : Parts X u u') (jn : ℝ) : Prop :=
  (∏ v, (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0) = jn

end Formalism.L2.SG.Pf.Carrier
