import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PProjBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumCl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PGeomPb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumHl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PiBCHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PDualSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PullbackComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PIntFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PCupEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateSurjectivePositiveDim

noncomputable section
open CrystallineSemistableComparison

namespace UpperTheory.Gal.KunnethLefschetz

theorem adicTop_holds : AdicTop :=
  adicTop_of ringL_holds projBC_holds sumCl_holds sumBC_holds geomPb_holds sumHl_holds piBC_holds dualSum_holds perm_holds
    intFun_holds cupEx_holds

theorem etSide_sm (hI : In) (hQ : QDual) (hS : InSum) (hC : ModelComponents) (hG : GeometricGenericComponents) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] : EtSide (Model.Sm (l := l) (K := K)) :=
  adicTop_holds hI hQ hS l K _ (fun _ h => h.1) (hC l K).1 fun M h d hd => hG l K M h.1 d hd

theorem etFin_of (hI : In) (hQ : QDual) (hS : InSum) (hC : ModelComponents) (hG : GeometricGenericComponents) : CrystallineSemistableComparison.Onto.EtFin :=
  fun l _ K _ M hM n => (etSide_sm hI hQ hS hC hG l K).fin M hM n

end UpperTheory.Gal.KunnethLefschetz
