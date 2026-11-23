import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def DedekindFibreRank.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (G : Type w) [AddCommGroup G] [Module S G],
    Module.Finite S G → Module.IsTorsionFree S G → ∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Module.length S (G ⧸ 𝔪 • (⊤ : Submodule S G)) = Module.finrank S G

end

end GroundTheory.Heights₂.Heights.Kleiman
