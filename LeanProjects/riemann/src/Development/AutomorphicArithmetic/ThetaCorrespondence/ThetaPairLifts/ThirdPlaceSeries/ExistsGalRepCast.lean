import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
theorem exists_galRep_cast_alt {D : D7} {a p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {ι : Qbar p ≃+* ℂ} {π : D.naut.CG a}
    {r : GalE D →* GL (Fin a) (Qbar p)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π p ι r) : ∃ r', _root_.UpperTheory.GalS.IsGaloisRepOfN D π q (qCast h ι) r' := by
  subst h
  exact ⟨r, hr⟩
end GlobalTheory.ResLoc
namespace GlobalTheory.ResLoc
end GlobalTheory.ResLoc
end
end
