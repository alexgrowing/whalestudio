import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PostOnMemEEatOfCenter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
set_option maxHeartbeats 800000
open Formalism.BasicNotions.TH Formalism.IndefR.Lev
namespace GlobalTheory.MiTop.CentralShift
section General
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
end General
section Main
open GlobalTheory.MiTop.CentralShift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem postOn_rTrL_mem_EEat_of_mem_center (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z : GA D (Yc D 0)} (hzf : z ∈ GfC (Yc D 0))
    (hzc : z ∈ Subgroup.center (GA D (Yc D 0))) (Pl : LevelP W.Q.Rl.toRealDat.Pg D.R.r ℂ) {T : MMap (W.Q.Rl.MY 0)}
    (hT : T ∈ W.Q.Rl.toRealDat.EEat Pl) :
    postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) T ∈ W.Q.Rl.toRealDat.EEat Pl := by
  unfold RealDat.EEat at hT ⊢
  refine GlobalTheory.MultTranslate.postOn_mem_goodPart hzf (fun k hk => ?_) (fun f => ?_) hT
  · have e : z⁻¹ * k * z = k := by
      rw [mul_assoc, Subgroup.mem_center_iff.mp hzc k, inv_mul_cancel_left]
    rw [e]
    exact ⟨hk, rfl⟩
  · unfold RealDat.e0
    exact gaL_rTr_of_center _ _ _ _ hzc f
end Main
end GlobalTheory.MiTop.CentralShift
namespace GlobalTheory.MiTop
open GlobalTheory.MiTop.CentralShift
theorem exists_isShift_of_center_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∃ V, _root_.GlobalTheory.MiTop.IsShiftOperator W z V := by
  intro D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc
  have hM := hB.hyp.2.2.2.1.models
  have hE := hM.HE
  have h0 := hM.ν0
  have hHaar : W.Q.Rl.ν0.IsHaarMeasure := h0.1.1
  have hFD := h0.2
  obtain ⟨hinj, hrange, hip⟩ := hE
  have he : ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat W.Q.Rl.toRealDat.triv := fun e => by
    rw [← hrange]; exact LinearMap.mem_range_self _ e
  have hmem : ∀ e, postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) ∈ LinearMap.range W.Q.Rl.HE.e :=
    fun e => by rw [hrange]; exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e)
  let Lr : W.Q.Rl.HE.H →ₗ[ℂ] LinearMap.range W.Q.Rl.HE.e :=
    (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) ∘ₗ W.Q.Rl.HE.e).codRestrict _ hmem
  let Vz : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H := (LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm.toLinearMap ∘ₗ Lr
  have hV : ∀ e, W.Q.Rl.HE.e (Vz e) = postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) := by
    intro e
    have h1 : ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) : LinearMap.range W.Q.Rl.HE.e) : MMap (W.Q.Rl.MY 0)) =
        W.Q.Rl.HE.e ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) := LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hzc' : z⁻¹ ∈ Subgroup.center (GA D (Yc D 0)) := Subgroup.inv_mem _ hzc
  have hipv : ∀ e e' : W.Q.Rl.HE.H,
      ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (W.Q.Rl.HE.e e) (W.Q.Rl.HE.e e') =
        ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e))
          (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e')) := by
    intro e e'
    have m1 := (Submodule.mem_inf.mp (he e)).1
    have m2 := (Submodule.mem_inf.mp (he e')).1
    have m3 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e))).1
    have m4 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e'))).1
    apply ipM_eq_of_iff
    intro c
    constructor
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z 1 (by simp) (map_mul_right_center _ hHaar hzc)
        _ m1 _ m2 _ _ (fun v g => by rw [one_mul]; rfl) (fun v g => by rw [one_mul]; rfl) c
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z⁻¹ 1 (by simp) (map_mul_right_center _ hHaar hzc')
        _ m3 _ m4 _ _ (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e v) (inv_mul_cancel_right g _).symm)
        (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e' v) (inv_mul_cancel_right g _).symm) c
  refine ⟨Vz, fun e v => ?_, fun e => ?_, fun e hel => ?_⟩
  · unfold _root_.GlobalTheory.MiTop.rowFormOfVector
    rw [hV]
    exact lift_postOn _ _ _
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hip, hip, hV, ← hipv]
  · rw [hV]
    exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ hel
end GlobalTheory.MiTop
end
end
