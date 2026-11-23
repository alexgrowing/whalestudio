import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl

namespace Formalism.HN

theorem satR : SatR := real_saturation_property
theorem finSup : FinSup := finite_supremum_slopes
theorem satBasic : SatBasic := saturation_basic_properties
theorem ratioMax : RatioMax := maximal_slope_ratio
theorem degSupermod : DegSupermod := degree_supermodular
theorem muChar : MuChar := slope_characterization
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
theorem slopeIneq : SlopeIneq := slope_inequality_general
theorem hnSum : HNSum := polygon_slope_sum
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
theorem duality : Duality := slope_duality_formula
theorem piSum : PiSum := product_slope_sum
theorem plLat : PlLat := place_lattice_structure
theorem sizeMu : SizeMu := size_maximal_slope
theorem gramBlock : GramBlock := gram_block_determinant
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
theorem htGram : HtGram := height_gram_determinant
theorem htImage : HtImage := height_image_formula
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
theorem rerealize : Rerealize := lattice_rerealization
theorem quotRealize : QuotRealize := quotient_lattice_realization
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
theorem theoremF : TheoremF := frame_theorem_log_ideal
theorem dualPl : DualPl := dual_polygon_identity

end Formalism.HN
