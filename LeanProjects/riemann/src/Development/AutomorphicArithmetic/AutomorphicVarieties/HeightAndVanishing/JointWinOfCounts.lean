import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountI
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PZeroLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountVs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountIV
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SumOut
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

open Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.HV

theorem pointHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) : PointHV :=
  point (sumIn h2 h5 (countVs hP hF hT CK hK) countIV) (sumOut h1 hZ h2 h3)

theorem thmHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) (K : BConst) {Ct : ℝ}
    (hC : 0 < Ct) : ThmHV K Ct :=
  thmHV (pointHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ) K Ct hC

theorem jointWin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV)
    (hZ : CountZ) : JointWin 401 :=
  jointWin_of (by norm_num) hB (thmHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ K (by norm_num))

theorem vwin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (hc : ThmBcFree) (h1 : CountI) (h2 : CountII) (h3 : CountIII)
    (h5 : CountV) (hZ : CountZ) : VWin :=
  vwin_of_joint (jointWin_of_counts hP hF hT hK hB h1 h2 h3 h5 hZ) ((thmBc_iff (by norm_num)).2 hc)

end UpperTheory.V.HV
