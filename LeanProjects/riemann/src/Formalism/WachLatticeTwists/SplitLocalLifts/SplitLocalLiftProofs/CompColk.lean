import Formalism.WachLatticeTwists.SplitLocalLifts.StatCompColk
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.NatCastPowSmul
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
import Formalism.WachLatticeTwists.LatticeDualFibres.PropLocContOfLattices

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem compColK : StatCompColK := by
  intro ℓ _ O _ _ A T' G _ _ _ _ P _ _ _ _ _ _ L _ _ _ _ _ _ r χ Dl inc v₁ ev hev hsurj Hf₁ Hf₂ e' j κ κz
    hκz hκ hS
  obtain ⟨Kc, Kz, h1, h2, h3⟩ := colK O A T' G P L r χ Dl inc v₁ ev hev hsurj Hf₁ Hf₂ ℓ e' j κ κz hκz hκ
    (srcO ℓ O _ _ Hf₁ Hf₂ _ e' hS)
  exact ⟨Kc, ⟨Kz, h1, h2⟩, h3⟩

theorem compColk : StatCompColk := by
  intro ℓ _ O _ _ A T' G _ _ _ _ P _ _ _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hsurj Hf₁ Hf₂ e' u uz
    huz hu hS
  obtain ⟨k0, kz, h1, h2, h3, h4⟩ := colk O A T' G P M r χ E δO Dl inc ev hE hM hev hsurj Hf₁ Hf₂ ℓ e'
    u uz huz hu (srcO ℓ O _ _ Hf₁ Hf₂ _ e' hS)
  exact ⟨k0, ⟨kz, h1, h2⟩, h3, h4⟩

end Formalism.RepresentationBoundsCohomology.JL
