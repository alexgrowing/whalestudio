import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechHdegOfSub.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (T : SubSystem S x E) (n : ℕ),
    Nonempty (T.H n ≃ₗ[S] Cech.Hdeg (fun _ : Chart x => E) (fun I => (T.sub I).restrictScalars S)
      (Cech.idRes S E (support x)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
