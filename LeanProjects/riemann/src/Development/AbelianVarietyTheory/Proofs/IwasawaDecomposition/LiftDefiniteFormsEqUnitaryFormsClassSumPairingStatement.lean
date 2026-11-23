import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftDefiniteFormsEqUnitaryFormsClassSumPairing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftDefiniteForms_eq_unitaryForms_classSumPairing : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | exact GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | (intros; apply GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed <;> assumption)
