import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropicGlobalFormOfDoublingStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAnisoOfSiegelWeilFockAnisoNc

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_tower_compatibility : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D → GlobalTheory.BottomRallis.GlobalFormAniso D := by
  first | exact @_root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc | exact _root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc | (intros; apply _root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc <;> assumption)
end
