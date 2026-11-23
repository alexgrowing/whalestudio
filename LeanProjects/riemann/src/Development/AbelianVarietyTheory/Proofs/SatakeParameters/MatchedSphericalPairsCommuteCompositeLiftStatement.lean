import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_spherical_pairs_commute_composite_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  first | exact @GlobalTheory.Hk3.SysE.matched_commute | exact GlobalTheory.Hk3.SysE.matched_commute | (intros; apply GlobalTheory.Hk3.SysE.matched_commute <;> assumption)
