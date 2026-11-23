import Formalism.WachLatticeTwists.SplitClassesAll.HZeroFromWInputsStatement
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.HZeroFromWFull
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.TheoremNFiveTopSplitTb
import Formalism.WachLatticeTwists.DenseTopActions.DenseTopActionProofs.QPowInj
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.FreeMembershipHeightOne
import Formalism.WachLatticeTwists.DenseTopActions.DenseTopActionProofs.Imports

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Matrix Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JW Polynomial
open scoped TensorProduct

theorem tbWIn : StatTBWIn := by
  intro ℓ _ D u w s m e d U hIn
  apply hIn
  intro R r L En M0 h0 W A Y' F hX hA hY1 hY2 hHT X infm infX K T φ ψ hd hin hLES hT5 hCR
    hK hTI hT4 hT3 htf Gs _ _ _ M _ _ _ _ _ _ MB _ _ _ _ _ aM aB Fj Hs γs lg ε iGe iB Os _ _ cupL embB
    hlg hadd hH hgen hγ hsq hcup hpin hLa hRV _ _ _ _ exQ Hfs δ hexQ hcompat hspan hdim hLu hcorF hcr
    hC hL hdR hH2 hu hw hs hm
  subst hu hw hs hm
  exact tbWFull ℓ R r L En M0 h0 W U A Y' F hX hA hY1 hY2 hHT e d D X infm infX K T φ ψ hd hin hLES hT5 hCR
    hK hTI hT4 hT3 htf Gs M MB aM aB Fj Hs γs lg ε iGe iB Os cupL embB
    hlg hadd hH hgen hγ hsq hcup hpin hLa hRV exQ Hfs δ hexQ hcompat hspan hdim hLu hcorF hcr
    hC hL hdR hH2

theorem h_zero_from_w_inputs : HZeroFromWInputsStatement := by
  intro ℓ _ D w m Uτ hIn
  apply hIn
  intro R r L En M0 h0 W A Y' F FH hA hY1 hY2 ρ Sτ Pp Sp Cm Bm hX hP hS hB hHT h0U hne infm infX X
    hInf hT4 hUn hFl hLES hD hw hm
  subst hD hw hm
  exact h_zero_from_w_full ℓ R r L En M0 h0 W A Y' F FH hA hY1 hY2 ρ Sτ Pp Sp Cm Bm Uτ hX hP hS hB hHT h0U hne infm infX X
    hInf hT4 hUn hFl hLES

theorem h0WJ : HZeroFromWJumpsStatement := by
  intro ℓ _ D w m J h
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3, -, -, b6, b7, b8, b9, b10⟩ := h_zero_from_w_inputs ℓ D w m (jumpsDualTwist J) a3
  exact ⟨a1, a2, b1, b2, b3, b6, b7, b8, b9, b10⟩

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
