import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CuspidalRankFourRegularAlgebraic
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
open private half_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.V.Z.Win.Birth

def CuspidalRankFourRegularAlgebraicTotallyComplex {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] (π : CuspSub L 4) : Prop := (CG.mk π).IsRegAlg ∧ ImaginaryQuadraticEtaCharacter.AllWin π

example : type_of% @CuspidalRankFourRegularAlgebraic := @CuspidalRankFourRegularAlgebraicTotallyComplex

theorem mkReg {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {π : CuspSub L 4} (h : (CG.mk π).IsRegAlg) (_ : ImaginaryQuadraticEtaCharacter.AllWin π) :
    CuspidalRankFourRegularAlgebraic π := h

theorem mkReg' {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {π : CuspSub L 4} (h : (CG.mk π).IsRegAlg) (u : ImaginaryQuadraticEtaCharacter.AllWin π) :
    CuspidalRankFourRegularAlgebraicTotallyComplex π := ⟨h, u⟩

end UpperTheory.V.Z.Win.Birth
