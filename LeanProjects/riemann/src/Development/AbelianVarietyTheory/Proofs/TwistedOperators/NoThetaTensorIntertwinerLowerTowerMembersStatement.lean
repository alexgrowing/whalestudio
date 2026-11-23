import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  first | exact @GlobalTheory.LowerTower.no_map_lower | exact GlobalTheory.LowerTower.no_map_lower | (intros; apply GlobalTheory.LowerTower.no_map_lower <;> assumption)
