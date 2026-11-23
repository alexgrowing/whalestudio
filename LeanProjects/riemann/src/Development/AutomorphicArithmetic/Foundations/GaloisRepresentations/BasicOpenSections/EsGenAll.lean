import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsTotHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpSpecIf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.POpCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism

namespace UpperTheory.Gal.Mod

theorem specGood : GlobalTheory.EtC.SpecGood := spSpecIf UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality

theorem esGen_all : ESGen := esGen_holds specGood

end UpperTheory.Gal.Mod
