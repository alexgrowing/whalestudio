import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormFrameLatticeStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAtFrameLatNc

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
theorem _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, SiegelWeilFock D → ∀ A : HSp D, GlobalFormAt A (frameLat A) := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | exact _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalFormAt_frameLat_nc <;> assumption)
end
