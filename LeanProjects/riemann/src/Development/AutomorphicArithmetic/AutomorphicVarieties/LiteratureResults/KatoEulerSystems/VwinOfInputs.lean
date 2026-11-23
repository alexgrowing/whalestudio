import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoLitOOf
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.OneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.EigSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.NormEqOneOfKillsMu
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.InputsOfHida
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoefIsCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Seed3N
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

open UpperTheory.Top UpperTheory.V.HV UpperTheory.V.HV.U

namespace UpperTheory.V.Lit.KN.O

theorem corGK_of (h : InpN) (ha : Aut.AutomorphyUnramifiedCoefficients) : U3.CorGK := U3.corGK (U3.propGK h.number (oneChar h ha))

theorem caseI (h : InpN) (ha : Aut.AutomorphyUnramifiedCoefficients) : CountI := U3.countI (corGK_of h ha)

end UpperTheory.V.Lit.KN.O
