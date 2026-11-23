import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHilbertModelInjectiveContainsGoodForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHilbertModel_injective_contains_goodForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  first | exact @GlobalTheory.LiftHilbertModel.hilbert_model_lift | exact GlobalTheory.LiftHilbertModel.hilbert_model_lift | (intros; apply GlobalTheory.LiftHilbertModel.hilbert_model_lift <;> assumption)
