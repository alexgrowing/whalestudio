import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.ExistsAuxiliaryPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCjMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDiscInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBarAdj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.MemIffDvd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSides

open UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1

namespace UpperTheory.Gal.Int.Geo.Pl

theorem datEx_holds : DatEx := datEx_of exists_auxiliary_prime ArithK_holds SetupEx_holds ScOf_holds PerfCof_holds

theorem sides_holds : Sides := pSides pCjMem (pBarAdj pDiscInt) (pKeyK pDiscInt) RootAt_holds

end UpperTheory.Gal.Int.Geo.Pl
