import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtValAtNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDegreeCmLogPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateShiftCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftStOfPublished

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore

theorem flatDegreeSt_of_prismaticDieudonne :
    GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne →
      GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt := by
  intro hSW hP2 hQ2 hQ3 hPD
  intro E _ _ _ H hH _ χ hχ Dw l Xo c r U x hL
  have hPS : GlobalTheory.FlatCM.PlaceShiftSt := GlobalTheory.placeShiftSt_of_scholzeWeinstein hP2 hSW
  have hCM : CMDiffSt := GlobalTheory.T.cm_different_from_ideal (GlobalTheory.T.ideal_from_place_shift hPS)
  have hArch : ArchEx U x := GlobalTheory.T.archimedean_existence_everywhere E H Dw l Xo c r U x hL
  have hHT : HTConst U x := GlobalTheory.T.hodge_tate_constant_everywhere hP2 hQ2 hQ3 hPD E H Dw l Xo c r U x hL
  have hSh : HTShift Xo c := GlobalTheory.T.hodge_tate_shift_cm hP2 hPS E H hH Dw l Xo c
  have hFin : FinConst U x := GlobalTheory.FlatCore.Fin.finConst_main E H Dw l Xo c r U x hL hSh hHT
  have hFr : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := GlobalTheory.T.frame_degree_cm_log_period hCM E H hH χ hχ Dw l Xo c r U x hL
  exact GlobalTheory.FlatCore.flatDegree_of_steps E H Dw l Xo c r U x hL _ hArch hFin hFr

end GlobalTheory.FlatCore
