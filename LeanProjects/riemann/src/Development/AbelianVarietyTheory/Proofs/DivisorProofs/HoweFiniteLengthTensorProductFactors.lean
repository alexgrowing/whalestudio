import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactorStatement

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensAlg

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_eq_toLinearMap (w : T) (L : Module.End ℂ (V w)) :
    atPl w L = (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L := rfl

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  unfold atPl
  have h : Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id := by
    funext i
    by_cases hi : i = w
    · subst hi; simp; rfl
    · simp [hi]
  rw [h]; exact PiTensorProduct.map_id

theorem atPl_sub_smul (w : T) (L : Module.End ℂ (V w)) (c : ℂ) (y : ⨂[ℂ] i, V i) :
    atPl w (L - c • 1) y = atPl w L y - c • y := by
  rw [atPl_eq_toLinearMap, map_sub, map_smul, ← atPl_eq_toLinearMap, ← atPl_eq_toLinearMap, atPl_one]
  simp

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp
  · simp [hi]

theorem atPl_tprod_eq_zero (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) (h : L (v w) = 0) :
    atPl w L (PiTensorProduct.tprod ℂ v) = 0 := by
  rw [atPl_tprod, h]
  exact MultilinearMap.map_update_zero _ _ _

theorem tensAll_mono {H H' : ∀ w, Submodule ℂ (V w)} (h : ∀ w, H w ≤ H' w) : tensAll H ≤ tensAll H' := by
  apply Submodule.span_mono
  rintro y ⟨f, hf, rfl⟩
  exact ⟨f, fun w => h w (hf w), rfl⟩

theorem iInf_hwSub_le {R S : T → ℕ} (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (μ : ∀ w, Ix (R w) (S w) → ℚ) :
    (⨅ w, hwSub (actAt w (a w)) (μ w)) ≤ tensAll (fun w => hwSub (a w) (μ w)) := by
  intro y hy
  rw [Submodule.mem_iInf] at hy
  refine GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel T V
    (fun w => {l | (∃ c, l = a w (Eab c c) - ((μ w c : ℚ) : ℂ) • 1) ∨ ∃ c d, posC c d ∧ l = a w (Eab c d)})
    (fun w => hwSub (a w) (μ w)) ?_ y ?_
  · intro w x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun c => ?_, fun c d hcd => ?_⟩
    · exact hx _ (Or.inl ⟨c, rfl⟩)
    · exact hx _ (Or.inr ⟨c, d, hcd, rfl⟩)
  · intro w l hl
    have hyw := hy w
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyw
    rcases hl with ⟨c, rfl⟩ | ⟨c, d, hcd, rfl⟩
    · rw [atPl_sub_smul]
      have h1 := hyw.1 c
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply] at h1
      exact h1
    · have h2 := hyw.2 c d hcd
      rw [actAt_apply] at h2
      exact h2

end GlobalTheory.HoweR.TensAlg

namespace GlobalTheory.HoweR

open GlobalTheory.HoweR.TensAlg in

theorem howeAlg_tensAny : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  intro T _ _ V _ _ R S a C hP
  have hG := GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute T V R S a (fun w => (hP w).1)
  choose α β α' β' hQ using fun w => (hP w).2.2.1
  choose μ v hv hgen hmul using fun w => (hP w).2.2.2.2
  refine GlobalTheory.T.howeAlg_of_cyclic_highest_weight T R S (⨂[ℂ] i, V i) (fun w => actAt w (a w)) hG.1 hG.2 (tensAny C) α β α' β'
    (fun w => GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor T V C w (R w) (S w) (a w) _ _ _ _ (hQ w)) ?_ ?_
  · intro B
    choose U hUfd hU using fun w => (hP w).2.2.2.1 B
    refine ⟨tensAll U, (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).2.1 hUfd, fun ν hν => ?_⟩
    exact (iInf_hwSub_le a ν).trans
      ((tensAll_mono (fun w => hU w (ν w) (fun c => hν w c))).trans (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).1)
  · refine ⟨μ, PiTensorProduct.tprod ℂ v, fun w => ?_,
      fun N hN hC hvN => GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor T V R S a C v hgen N hN hC hvN, ?_⟩
    · have h := hv w
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h ⊢
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply, ← atPl_sub_smul]
        exact atPl_tprod_eq_zero w _ v (h.1 c)
      · rw [actAt_apply]
        exact atPl_tprod_eq_zero w _ v (h.2 c d hcd)
    · refine (iInf_hwSub_le a μ).trans ((tensAll_mono (fun w => hmul w)).trans ?_)
      refine (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).1.trans ?_
      exact sup_le_sup_right ((GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).2.2 v) _

end GlobalTheory.HoweR

end
