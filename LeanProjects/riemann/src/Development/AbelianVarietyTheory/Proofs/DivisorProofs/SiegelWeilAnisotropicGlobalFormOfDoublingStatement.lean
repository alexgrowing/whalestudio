import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropicGlobalFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_anisotropic_global_form_of_doubling : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DoublingMethod → ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D → GlobalTheory.BottomRallis.GlobalFormAniso D := by
  first | exact @GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso | exact GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso | (intros; apply GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso <;> assumption)
