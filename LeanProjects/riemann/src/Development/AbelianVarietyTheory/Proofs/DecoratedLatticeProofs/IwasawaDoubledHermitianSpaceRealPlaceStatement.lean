import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ w : InfinitePlace D.host.F, HasIwasawa D.sp.cm.sig (dblSp A).gram (KArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a)) := by
  first | exact @GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch | exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch | (intros; apply GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch <;> assumption)
