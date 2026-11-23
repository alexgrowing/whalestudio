import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
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
theorem _root_.GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i, ∃ h, IsOpsW R i h ∧ NormalFam (Good R A.μ0) h ∧ (∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g)) ∧ (⨆ c, Wcc R SF i c) = LinearMap.range (eH R i) ∧ (∀ c g, (Wcc R SF i c).map (R.gW i (sg0 D A) g) ≤ Wcc R SF i c) ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ Wcc R SF i c, h P cc x = evC (Wc D i) P (c P) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, eH R i x = x → (∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x) → x ∈ Wcc R SF i c := by
  first | exact @GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt | exact GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt | (intros; apply GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt <;> assumption)
