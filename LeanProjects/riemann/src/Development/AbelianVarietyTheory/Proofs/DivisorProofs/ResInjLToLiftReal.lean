import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftResInj

theorem resInjL_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.models_inf → RecTie.ResInjL (RecTie.toLiftReal R F tupT hm hTop hinj) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hθ i w hw h0
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w
  have hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A)) _ _ := (Mult.mem_multT _ _ _ _ w).1 hw
  have hT : U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
      have e := LinearMap.congr_fun h0 (PiTensorProduct.tprod ℂ v)
      have e2 : w (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
      rw [PiTensorProduct.map_tprod] at e2
      show (PiTensorProduct.lift.symm w : MMap (R.MW i (sg0 D A))) (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0
      exact e2)
  have e3 : PiTensorProduct.lift U = w := LinearEquiv.apply_symm_apply _ w
  rw [← e3, hT]
  exact map_zero _

end GlobalTheory.LiftResInj

end
