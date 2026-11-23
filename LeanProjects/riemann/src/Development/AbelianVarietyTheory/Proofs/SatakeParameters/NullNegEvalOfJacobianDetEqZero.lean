import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomeomorphZeroSet
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open MeasureTheory Topology

namespace GlobalTheory.ChartSard

theorem null_negEv_of_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  intro X p d U ch φ
  set T : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap with hT
  have hTw : ∀ w, T w = WithLp.toLp 2 w := fun w => rfl
  set g : Fin d → EuclideanSpace ℂ (Fin d) → ℂ :=
    fun j => GlobalTheory.CxPts.ev p (RingHom.id ℂ) U (φ j) ∘ ch.e.symm with hg
  set H : (Fin d → ℂ) → (Fin d → ℂ) := fun w j => -g j (T w) with hH
  refine ⟨H '' {w | DifferentiableAt ℝ H w ∧ (fderiv ℝ H w).det = 0},
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun w => fderiv ℝ H w)
      (fun w hw => hw.1.hasFDerivAt.hasFDerivWithinAt) (fun w hw => hw.2), ?_⟩
  intro z hzs hz hdet
  set w : Fin d → ℂ := (ch.e z).ofLp with hw
  have hTz : T w = ch.e z := rfl
  have hL : ∀ j, HasFDerivAt (g j) (fderiv ℂ (g j) (ch.e z)) (T w) := fun j => by
    rw [hTz]; exact (ch.differentiableAt_ev (φ j) hzs hz).hasFDerivAt
  set M : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun j => -((fderiv ℂ (g j) (ch.e z)).comp T) with hM
  have hHM : HasFDerivAt H M w := by
    refine hasFDerivAt_pi'.2 fun j => ?_
    exact ((hL j).comp w T.hasFDerivAt).neg
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hTv : T v = ∑ b, v b • EuclideanSpace.single b (1 : ℂ) := by
    ext i
    simp [hTw, EuclideanSpace.single_apply, Pi.single_apply]
  have hMv : M v = 0 := by
    funext j
    have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hj
    simp only [hM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, hTv, map_sum, map_smul, smul_eq_mul, Pi.zero_apply, neg_eq_zero]
    rw [← hj]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨w, ⟨(hHM.restrictScalars ℝ).differentiableAt, ?_⟩, ?_⟩
  · rw [(hHM.restrictScalars ℝ).fderiv]
    refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩)
    show M v = 0
    exact hMv
  · funext j
    simp only [hH, hg, Function.comp_apply, hTz, ch.e.left_inv hzs, GlobalTheory.CxPts.ev_eq hz]

end GlobalTheory.ChartSard
