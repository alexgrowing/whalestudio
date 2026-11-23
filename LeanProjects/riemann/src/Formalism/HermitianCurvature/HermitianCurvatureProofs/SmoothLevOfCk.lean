import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def retV (g₀ : B.Mat k r) : Set (B.Mat k r) := {Y | IsUnit (g₀⁻¹ * Y + 1).det}

def retDom (g₀ : B.Mat k r) : Set (B.Mat k r) :=
  retV g₀ ∩ (fun Y => prj (iot (g₀⁻¹ * Y))) ⁻¹' {X | IsUnit (1 - X).det}

def ret (g₀ : B.Mat k r) (Y : B.Mat k r) : B.Mat k r := g₀ * kap (prj (iot (g₀⁻¹ * Y)))

lemma isOpen_unitDet {X : Type*} [TopologicalSpace X] {f : X → B.Mat k r} (hf : Continuous f) :
    IsOpen {x | IsUnit (f x).det} := by
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

lemma isOpen_retV (g₀ : B.Mat k r) : IsOpen (retV g₀) := isOpen_unitDet ((continuous_const.mul continuous_id).add continuous_const)

lemma cd_iotL (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (fun Y => iot (g₀⁻¹ * Y)) (retV g₀) := by
  have h1 : ContDiffOn ℝ ∞ (fun Y : B.Mat k r => g₀⁻¹ * Y) (retV g₀) := cdm_mul contDiffOn_const contDiffOn_id
  show ContDiffOn ℝ ∞ (fun Y => (g₀⁻¹ * Y - 1) * (g₀⁻¹ * Y + 1)⁻¹) (retV g₀)
  exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun Y hY => hY)

lemma isOpen_retDom (g₀ : B.Mat k r) : IsOpen (retDom g₀) := by
  exact (cdm_prj (cd_iotL g₀)).continuousOn.isOpen_inter_preimage (isOpen_retV g₀)
    (isOpen_unitDet (f := fun X : B.Mat k r => 1 - X) (continuous_const.sub continuous_id))

lemma cd_ret (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (ret g₀) (retDom g₀) := by
  have hA : ContDiffOn ℝ ∞ (fun Y => prj (iot (g₀⁻¹ * Y))) (retDom g₀) :=
    cdm_prj ((cd_iotL g₀).mono Set.inter_subset_left)
  show ContDiffOn ℝ ∞ (fun Y => g₀ * ((1 + prj (iot (g₀⁻¹ * Y))) * (1 - prj (iot (g₀⁻¹ * Y)))⁻¹)) (retDom g₀)
  exact cdm_mul contDiffOn_const
    (cdm_mul (contDiffOn_const.add hA) (cdm_inv (contDiffOn_const.sub hA) fun Y hY => hY.2))

lemma ret_mem {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ retDom g₀) :
    ret g₀ Y ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.B2x8.al_mul_mem hg₀ (kap_mem (prj_lie (iot (g₀⁻¹ * Y))) hY.2)

private lemma prj_eq_self_of_inLie {X : B.Mat k r} (hX : B.inLie k r X) : prj X = X := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have h2 : Hpk k r * Xᴴ * Hpk k r = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Ux10.hpk_sq', Matrix.one_mul]
  unfold prj
  rw [h2, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

lemma ret_self {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ B.GV k r)
    (hu : IsUnit (g₀⁻¹ * Y + 1).det) : ret g₀ Y = Y := by
  have hh : g₀⁻¹ * Y ∈ B.GV k r := Formalism.FourierDecayAlt.P.B2x8.al_mul_mem (Formalism.FourierDecayAlt.P.B2x8.al_inv_mem hg₀) hY
  obtain ⟨hl, -, hk⟩ := iot_facts hh hu
  show g₀ * kap (prj (iot (g₀⁻¹ * Y))) = Y
  rw [prj_eq_self_of_inLie hl, hk, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀), Matrix.one_mul]

lemma self_mem_retDom {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : g₀ ∈ retDom g₀ := by
  have e : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀)
  refine ⟨?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1).det
    rw [e, ← two_smul ℂ (1 : B.Mat k r), Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
  · show IsUnit (1 - prj (iot (g₀⁻¹ * g₀))).det
    rw [e, show iot (1 : B.Mat k r) = 0 by simp [iot], prj_zero, sub_zero, Matrix.det_one]
    exact isUnit_one

lemma ret_at {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : ret g₀ g₀ = g₀ := ret_self hg₀ hg₀ (And.left (self_mem_retDom hg₀))

lemma glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

theorem smoothLev_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : ∀ m : ℕ, CkLev k r 0 m D f) : SmoothLev k r 0 D f := by
  intro g₀ hg₀
  have hG₀ : g₀ ∈ B.GV k r := hg₀.1.1
  have hU : IsOpen (retDom g₀ ∩ ret g₀ ⁻¹' D) :=
    (cd_ret g₀).continuousOn.isOpen_inter_preimage (isOpen_retDom g₀) hD
  refine ⟨retDom g₀ ∩ ret g₀ ⁻¹' D, fun Y => f (ret g₀ Y), hU, ⟨self_mem_retDom hG₀, ?_⟩, ?_, ?_⟩
  · show ret g₀ g₀ ∈ D
    rw [ret_at hG₀]
    exact hg₀.2
  · intro Y hY
    refine ContDiffAt.contDiffWithinAt ?_
    have hr : ContDiffAt ℝ ∞ (ret g₀) Y := (cd_ret g₀).contDiffAt ((isOpen_retDom g₀).mem_nhds hY.1)
    refine contDiffAt_infty.2 fun m => ?_
    have hZ : ret g₀ Y ∈ Glev k r 0 ∩ D := ⟨glev0 (ret_mem hG₀ hY.1), hY.2⟩
    obtain ⟨U, F, hUo, hZU, hF, hfF⟩ := hf m (ret g₀ Y) hZ
    have hc : ContDiffAt ℝ m (fun Y' => F (ret g₀ Y')) Y :=
      (hF.contDiffAt (hUo.mem_nhds hZU)).comp Y (contDiffAt_infty.1 hr m)
    refine hc.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ Y' in 𝓝 Y, Y' ∈ retDom g₀ := (isOpen_retDom g₀).mem_nhds hY.1
    have h2 : ∀ᶠ Y' in 𝓝 Y, ret g₀ Y' ∈ U := hr.continuousAt.preimage_mem_nhds (hUo.mem_nhds hZU)
    filter_upwards [h1, h2] with Y' h1' h2'
    exact hfF _ h2' (glev0 (ret_mem hG₀ h1'))
  · intro g hg hgl
    show f g = f (ret g₀ g)
    rw [ret_self hG₀ hgl.1 hg.1.1]

end Formalism.FourierDecayAlt.P5.Rad
