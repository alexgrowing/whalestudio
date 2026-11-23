import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
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
theorem _root_.GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∃ h, IsOpsE R h ∧ NormalFam (Good R A.μ0) h ∧ (⨆ c, EEc R SF c) = ⊤ ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ EEc R SF c, h P cc x = evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, Good R A.μ0 P → IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ EEc R SF c := by
  first | exact @GlobalTheory.Hk3.OpsRows.exists_opsE | exact GlobalTheory.Hk3.OpsRows.exists_opsE | (intros; apply GlobalTheory.Hk3.OpsRows.exists_opsE <;> assumption)
