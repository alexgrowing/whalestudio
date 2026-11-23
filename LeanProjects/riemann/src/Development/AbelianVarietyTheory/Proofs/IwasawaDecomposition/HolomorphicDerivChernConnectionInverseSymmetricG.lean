import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

open Filter

theorem del_del_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u : E → ℂ} {z : E} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    GlobalTheory.del (fun x => GlobalTheory.del u x w) z v = GlobalTheory.del (fun x => GlobalTheory.del u x v) z w := by
  have h := GlobalTheory.differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ w, (fun x => GlobalTheory.del u x w) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w)) :=
    fun w => funext fun x => GlobalTheory.del_apply u x w
  have d : ∀ w, GlobalTheory.del (fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w))) z
      = (1 / 2 : ℂ) • (GlobalTheory.del (fun x => fderiv ℝ u x w) z
          - Complex.I • GlobalTheory.del (fun x => fderiv ℝ u x (Complex.I • w)) z) := fun w => by
    rw [GlobalTheory.del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      GlobalTheory.del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), GlobalTheory.del_const_smul _ (h1 _)]
  rw [e w, e v, d w, d v]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, GlobalTheory.del_apply,
    GlobalTheory.fderiv_fderiv_apply hu]
  rw [hs.eq v w, hs.eq (Complex.I • v) w, hs.eq v (Complex.I • w),
    hs.eq (Complex.I • v) (Complex.I • w)]
  match_scalars <;> ring

theorem mdel_mdel_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {m n : Type*} {A : E → Matrix m n ℂ} {z : E} (h : MContDiffAt 2 A z)
    (ξ η : E) : mdel (fun x => mdel A x η) z ξ = mdel (fun x => mdel A x ξ) z η := by
  ext a b
  exact del_del_comm (h a b) ξ η

theorem mdel_conn_inv_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E)
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ η : E) :
    mdel (fun x => conn (fun y => (H y)⁻¹) x η) z ξ
      - mdel (fun x => conn (fun y => (H y)⁻¹) x ξ) z η
      = -(conn H z η * conn H z ξ - conn H z ξ * conn H z η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hloc : ∀ ζ, (fun x => conn (fun y => (H y)⁻¹) x ζ) =ᶠ[𝓝 z]
      fun x => -((H x)⁻¹ * mdel H x ζ)ᵀ := fun ζ => by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu, hs.eventually_nhds]
      with x hx2 hxu hxs
    have e : (fun y => (H y)⁻¹) =ᶠ[𝓝 x] fun y => GlobalTheory.HermFrame.dualGram (H y) :=
      hxs.mono fun y hy => by
        change (H y)⁻¹ = (H y)⁻¹ᵀ
        rw [transpose_nonsing_inv, hy.eq]
    rw [conn_congr e, conn_dual (hx2.of_le one_le_two) hxu, conn_eq_of_isSymm hxs]
  have hP : ∀ ζ, MContDiffAt 1 (fun x => mdel H x ζ) z := fun ζ => h2.mdel (by norm_num) ζ
  rw [mdel_congr (hloc η), mdel_congr (hloc ξ), mdel_neg, mdel_neg,
    mdel_transpose (fun x => (H x)⁻¹ * mdel H x η), mdel_transpose (fun x => (H x)⁻¹ * mdel H x ξ),
    mdel_mul (h1.inv hu) (hP η), mdel_mul (h1.inv hu) (hP ξ), mdel_inv h1 hu, mdel_inv h1 hu,
    mdel_mdel_comm h2 ξ η, conn_eq_of_isSymm hs, conn_eq_of_isSymm hs]
  have key : (H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z ξ * (H z)⁻¹) * mdel H z η
      - ((H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z η * (H z)⁻¹) * mdel H z ξ)
      = (H z)⁻¹ * mdel H z η * ((H z)⁻¹ * mdel H z ξ) - (H z)⁻¹ * mdel H z ξ * ((H z)⁻¹ * mdel H z η) := by
    noncomm_ring
  rw [← key, transpose_sub]
  abel

end GlobalTheory.HermFrame
