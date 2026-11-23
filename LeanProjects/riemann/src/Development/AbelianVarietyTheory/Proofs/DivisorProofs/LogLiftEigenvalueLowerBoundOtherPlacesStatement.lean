import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  first | exact @GlobalTheory.LowOff.l6m_le_log_lam3_other_places | exact GlobalTheory.LowOff.l6m_le_log_lam3_other_places | (intros; apply GlobalTheory.LowOff.l6m_le_log_lam3_other_places <;> assumption)
