import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CIn
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FinAllOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGeoSide
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiStepOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

namespace UpperTheory.Ru.crystallineComparison

theorem finAll : UpperTheory.Gal.crystallineComparison.Br.FinAll := finAll_of fun l _ K _ r f hf => cIn l K r f hf

theorem smoothModel_crystalline : CrystallineSemistableComparison.SmoothModelCrystalline := (CrystallineSemistableComparison.cstSmooth_of_side fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K).1

theorem phiStep : UpperTheory.Gal.Int.Geo.PhiStep := phiStep_of (UpperTheory.Gal.Int.Geo.geoSide_of finAll smoothModel_crystalline)

end UpperTheory.Ru.crystallineComparison
