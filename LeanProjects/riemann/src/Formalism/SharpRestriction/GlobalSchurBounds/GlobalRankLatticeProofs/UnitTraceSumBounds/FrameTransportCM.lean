import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.MainNotions.Ext

def FrameTransportCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → FrameTransport F E σ

end Formalism.MainNotions.Ext
