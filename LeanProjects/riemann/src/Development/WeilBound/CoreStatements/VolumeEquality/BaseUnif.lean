import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifAsm
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConj
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifCoord
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec

namespace SheetDecomposition

theorem baseUnifEx2 : BaseUnifEx2 := baseUnifEx2_of (vecOfPeriods_of holCoord) kUnifConj

theorem baseUnifEx : BaseUnifEx := fun hG E _ _ _ H D l Xo c Y sm j j' n h₁ h₂ h₃ =>
  (baseUnifEx2 hG E H D l Xo c Y sm j j' n h₁ h₂ h₃).elim fun B _ => ⟨B⟩

end SheetDecomposition
