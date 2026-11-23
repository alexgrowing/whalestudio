import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.CoordW

set_option maxHeartbeats 2000000 in

theorem exists_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ mj : GlobalTheory.RealGeo.MjTie R.toRealDat F.lv2, ∃ jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1), ∀ (i : Fin D.R.m) v, mj.eW i (jW i v) = (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) v) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH mj
  have key : ∀ i : Fin D.R.m, ∃ g : (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL]
      D.what₂.Mj ((i : ℕ) + 1), ∀ v, mj.eW i (g v) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v := by
    intro i
    have he : Function.Injective (mj.eW i) :=
      GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (mj.eW_norm i)
    have hspan : Submodule.span ℂ (Set.range fun k =>
        GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1)) = LinearMap.range (mj.eW i) :=
      (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
        ((hH.aux.levelW false i _).trans (mj.eW_range i).symm)
    have hmem : ∀ v, GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v ∈ LinearMap.range (mj.eW i) := by
      intro v
      rw [← hspan, GlobalTheory.Mem.LiftTheta.semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    choose s hs using fun v => LinearMap.mem_range.1 (hmem v)
    exact ⟨{ toFun := s
             map_add' := fun a b => he ((hs (a + b)).trans (((map_add _ a b).trans
               (congrArg₂ (· + ·) (hs a).symm (hs b).symm)).trans (map_add (mj.eW i) (s a) (s b)).symm))
             map_smul' := fun c a => he ((hs (c • a)).trans (((LinearMap.map_smulₛₗ _ c a).trans
               (congrArg (D.what₂.embLL c • ·) (hs a).symm)).trans (LinearMap.map_smul (mj.eW i) _ (s a)).symm)) }, hs⟩
  choose jW hjW using key
  exact ⟨jW, fun i v => (hjW i v).trans
    (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _).symm)⟩

end GlobalTheory.Mem.CoordW
