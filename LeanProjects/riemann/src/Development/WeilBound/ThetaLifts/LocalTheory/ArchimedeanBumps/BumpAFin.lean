import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.BumpAOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceMain

namespace PositivityTheory.ThKG.Loc.Bump

open GlobalTheory.ThK PositivityTheory.ThKCT PositivityTheory.ThKF

theorem bumpA_fin (h₁ : StabEx) (h₂ : ArchOp) (h₃ : Slice) (h₄ : ArchUniq) (h₅ : SchInt) (h₆ : MixAB) : BumpA :=
  bumpA_of h₂ (eiDense_of h₅) (archSlice_of h₁ h₂ h₃ archHeis_of h₄ h₅) h₆

theorem bumpB_fin (h₁ : StabEx) (h₂ : ArchOp) (h₃ : Slice) (h₄ : ArchUniq) (h₅ : SchInt) (h₆ : MixAB) : BumpB :=
  bumpB_of h₂ (eiDense_of h₅) (archSlice_of h₁ h₂ h₃ archHeis_of h₄ h₅) h₆

end PositivityTheory.ThKG.Loc.Bump
