import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

namespace GlobalTheory.GalOfCusp

theorem localGlobalAboveL_of_potSemistable_of_purity (H : GlobalTheory.Published.LocalGlobalAboveLPst) (hC : GlobalTheory.Published.RegularAlgebraicPurity) :
    LocalGlobalAboveL :=
  H.localGlobalAboveL.regAlg hC

theorem localGlobalAboveL_of_caraiani_of_clozel : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.GalOfCusp.LocalGlobalAboveL :=
  fun H => H.car.regAlg H.clo

end GlobalTheory.GalOfCusp
