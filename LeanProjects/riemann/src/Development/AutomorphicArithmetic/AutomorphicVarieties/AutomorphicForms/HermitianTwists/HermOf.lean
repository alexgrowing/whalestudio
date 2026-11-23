import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

open UpperTheory.V UpperTheory.V.Af
open private lie_one from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig

theorem UpperTheory.V.Af.Rn.hermOf :
    UpperTheory.V.Af.Rn.HermOf := by
  intro c π hπ
  exact Br.hermEx ℚ 2 one_le_two π fun φ hφ => lie_one φ fun v => by
    rw [(Br.capTwo ℚ π v _ _ (hπ v) φ hφ).1, add_neg_cancel, zero_smul]
