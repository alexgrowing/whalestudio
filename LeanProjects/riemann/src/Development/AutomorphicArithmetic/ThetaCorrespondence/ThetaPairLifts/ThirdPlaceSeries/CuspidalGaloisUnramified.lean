import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
namespace At
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section RepOps
variable {Γ : Type} [Group Γ] {k : Type} [CommRing k]
end RepOps
def provisionFortyOne (i : N.Loc) : Prop :=
  ((∃ rq : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, IsHeckeGaloisQ N A i x (rq x)) ∧
    ∃ r, GoodR N i r) ∧
  (∀ P P' : A.AV i, A.ptV i P ≠ none → A.ptV i P = A.ptV i P' →
    (∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ N.S i → w ∉ N.Q i →
      (IsSplitPl H w → A.locV i P w = A.locV i P' w) ∧
      (¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w))) ∧
  ∀ r, GoodR N i r → G1 N i r ∧ _root_.UpperTheory.GalS.G2a N A i r ∧ _root_.UpperTheory.GalS.G3 N i r ∧ G4 N i r
end At
open Formalism.BasicNotions
def adm2_alt (D : D7) : Prop := _root_.UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut
def adm7_alt (D : D7) : Prop := _root_.UpperTheory.GalN.AllCuspidalOpenBound D.nd D.naut
def provisionFortyOne (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne D.nd D.naut i
def CuspidalGaloisUnramified' (D : D7) : Prop := ∀ i, _root_.UpperTheory.GalS.UnusedSlot55 D.nd D.naut i
def provisionFirst (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D ∧ Conclusion42 D
def AdmAAlt (D : D7) : Prop := tie0 D ∧ hypO D ∧ adm1 D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D
def AdmAtAlt (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
def AdmissibleDatum (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D ∧ adm6 D ∧ adm8 D
end Formalism.MainNotions.SumRepresentations
end
end
