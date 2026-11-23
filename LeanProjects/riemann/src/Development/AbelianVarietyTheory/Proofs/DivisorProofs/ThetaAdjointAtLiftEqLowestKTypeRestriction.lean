import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevelStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireLift

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  ext v
  simp [postOn]

theorem thetaFireL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireL (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hLev hGrp hMod hThP hv0 IL μ hμ i x
  have hfm : ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) ∈ LinearMap.range (R.extV i (tupT μ)) ⊓
      RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false)))
        (levChi _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false))) := (IL.jMt μ hμ i x).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm
      ⟨((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : R.extV i (tupT μ) y = ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (hinj i (tupT μ))).apply_symm_apply _)
  have hM := GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel R F hLev hMod hThP hv0 false i (tupT μ) y (by rw [hyf]; exact hfm.2)
  refine ⟨PiTensorProduct.lift (R.thF i (tupT μ) y), ?_, ?_, ?_⟩
  · exact Submodule.mem_map_of_mem hM
  · rw [← hy]; rfl
  · have hG : R.eWf i (sg0 D A) ∘ₗ PiTensorProduct.lift (R.thF i (tupT μ) y) ∈
        (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).map
          (PiTensorProduct.lift : MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap := by
      rw [← lift_postOn]
      exact Submodule.mem_map_of_mem (GlobalTheory.GoodProjLevel.proj_mem_good R hLev hGrp.record hv0 i _ _ hM)
    exact hG

end GlobalTheory.ThetaFireLift
