import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.ReducibleThreeDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.OneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.InputsOfHida
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoefIsCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Seed3N
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

open UpperTheory.Top UpperTheory.V.HV UpperTheory.V.HV.U

namespace UpperTheory.V.Z.Kato

theorem corGK_of (h : InpZ) (ha : Aut.AutomorphyUnramifiedCoefficients) : U3.CorGK := U3.corGK (U3.propGK h.number (oneChar h ha))

theorem caseI (h : InpZ) (ha : Aut.AutomorphyUnramifiedCoefficients) : CountI := U3.countI (corGK_of h ha)

end UpperTheory.V.Z.Kato
