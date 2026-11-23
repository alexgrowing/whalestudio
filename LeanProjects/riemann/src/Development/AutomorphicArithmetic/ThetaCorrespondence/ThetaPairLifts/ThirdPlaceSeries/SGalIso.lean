import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    ∀ i, UpperTheory.GalS.GalIsoN D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨ρ, c, s, o, -⟩ := UpperTheory.GalS.isoRep D hT (_root_.UpperTheory.GalS.weak' hG) i P Pa hB
  exact ⟨ρ, c, s, o⟩
end
