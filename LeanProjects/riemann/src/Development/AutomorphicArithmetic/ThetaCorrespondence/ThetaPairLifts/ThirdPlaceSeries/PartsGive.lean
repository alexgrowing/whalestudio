import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
structure RowsAAlt (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  g4p : _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
def SummandsSuffice (D : D7) : Prop :=
  _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D → SumRepresentations.tieLab D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, LamPos D (D.nd.mu i) (D.nd.j i)) →
    ThetaOne D → _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
structure LinkedData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 where
  P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X
structure LinkedDataNamed {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (T : _root_.GlobalTheory.NRows.LinkedData hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t
structure LinkedInputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 extends toRowSideFamily : _root_.GlobalTheory.NRows.LinkedData hL D where
  named : _root_.GlobalTheory.NRows.LinkedDataNamed toRowSideFamily
structure PointConditions' (D : D7) : Prop where
  a : _root_.GlobalTheory.NRows.RowsAAlt D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L
namespace Inputs
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (I : _root_.GlobalTheory.NRows.LinkedInputs hL D)
include I
theorem _root_.GlobalTheory.NRows.LinkedInputs.hypO : SumRepresentations.hypO D := I.named.hypO
theorem _root_.GlobalTheory.NRows.LinkedInputs.c1 : GlobalDatumCompatibility D := I.named.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.bc : SphericalInertData.Conclusion1 D := I.named.bc
theorem _root_.GlobalTheory.NRows.LinkedInputs.lam : LamUsed D := I.named.lam
theorem _root_.GlobalTheory.NRows.LinkedInputs.isot : SumRepresentations.adm8 D := I.named.isot
theorem _root_.GlobalTheory.NRows.LinkedInputs.ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser
theorem _root_.GlobalTheory.NRows.LinkedInputs.typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ
theorem _root_.GlobalTheory.NRows.LinkedInputs.e0loc : GoodIdempotentFixesLocalisationForms D := goodIdempotentFixes_of_onlySeriesOfLabelActs I.ser
set_option linter.unusedSectionVars false in
theorem _root_.GlobalTheory.NRows.LinkedInputs.mtPar : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie
theorem _root_.GlobalTheory.NRows.LinkedInputs.adm1 : SumRepresentations.adm1 D := base_change_automorphic_of D I.bc I.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.admAt (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D :=
  ⟨⟨a.tie0, I.hypO, I.adm1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩
theorem _root_.GlobalTheory.NRows.LinkedInputs.Conclusion1 (h : _root_.GlobalTheory.NRows.SummandsSuffice D) (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D :=
  h (I.admAt a b) a.tieLab b.rowSize a.hecke I.lam.loc b.thetaOne a.g4p
end Inputs
end GlobalTheory.NRows
end
end
