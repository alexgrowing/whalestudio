import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.PtSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
theorem reducedMultiplicity_of_rows' :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  intro hL D I R i _
  have hInt : Rows.IsotInternal D.what₂ := I.isot
  have h42 : SumRepresentations.Conclusion42 D := (I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b).2.2
  have h1 := map_MjSig_eq D i hInt (h42 i) (R.c.parUp i) (R.c.downMem i) (R.typeNZ i)
  exact ⟨h1, (SumRepresentations.good_part_image_iff D.nd D.naut i hInt (h42 i) h1).2 (R.c.goodPart i)⟩
end GlobalTheory.PtSt
end
end
