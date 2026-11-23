import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaBridgeARC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) → RatTriv u X Λ β

def IotaBridgeRAC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      RatTriv u X Λ β → AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u))

end Formalism.L2.SG.Pf
