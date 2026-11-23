import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LowRes

theorem multW_lowRes_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP _ y i w hw hK
  have hM := hP.char.base.models
  set M := R.MW i (sg0 D A3.A)
  let w' : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap M := PiTensorProduct.lift.symm w'
  have hU : U ∈ Mult R.θ M _ _ := (Mult.mem_multT _ _ _ _ w').1 hw
  have h0 : U = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ M R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
        have e := LinearMap.congr_fun hK (PiTensorProduct.tprod ℂ v)
        have e2 : w' (PiTensorProduct.map (fun τ => (lowT M τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
        rw [PiTensorProduct.map_tprod] at e2
        have e3 : PiTensorProduct.lift U (PiTensorProduct.tprod ℂ (fun τ => (lowT M τ).subtype (v τ))) = 0 := by
          rw [show PiTensorProduct.lift U = w' from LinearEquiv.apply_symm_apply _ w']; exact e2
        rw [PiTensorProduct.lift.tprod] at e3
        exact e3)
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  show w' = 0
  rw [← hUw, h0, map_zero]

end GlobalTheory.Mem.R3.Rw.LowRes

end
