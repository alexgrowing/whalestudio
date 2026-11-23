import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceExhaustion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem contDiffOn_log_dualNorm {n : ℕ} (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {0}ᶜ := by
  intro x hx
  have hM : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this, h0, Matrix.mulVec_zero]; rfl)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  have hpos : 0 < ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hQ : ContDiff ℝ ∞ fun y : Fin n → ℂ => ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by
    refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)
  exact ((hQ.contDiffAt.sqrt hpos.ne').log (Real.sqrt_pos.mpr hpos).ne').contDiffWithinAt

theorem smoothNear_log_dualNorm_slice {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) :
    SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by
  refine ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx hx0 => ?_, contDiffOn_log_dualNorm h⟩
  have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [Set.mem_singleton_iff] at hx0
  subst hx0
  simp [linForm] at this

theorem SliceSectionMass.proof (hSt : StokesOnVariety.Statement) (hPL : PoincareLelong.Statement)
    (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement) (hE : SliceExhaustion.Statement) :
    SliceSectionMass.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨hinj, himg, hmult⟩ := hC n J u ℓ hJ hℓW
  obtain ⟨f, hfs, hfc, -, -, hlimJ, hlimW, herr⟩ := hE n e h J F u ℓ hJ hF hu hℓ hℓW
  have hsm := smoothNear_log_dualNorm_slice h J ℓ
  have hk : ∀ k, ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) +
      (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) =
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
        (fun _ x => Real.log (h.dualNorm x)) := by
    intro k
    have hS := hSt n e _ (f k) (fun x => Real.log (h.dualNorm x))
      (fun _ x => Real.log (h.dualNorm x)) hprime hdim (smoothNear_of_contDiff (hfs k)) hsm (fun _ => hsm)
      (Or.inl (hfc k))
    have hP := hPL n e _ u (f k) (fun _ x => Real.log (h.dualNorm x)) hprime hdim (huJ u hu) (hfs k)
      (hfc k) (fun _ => hsm)
    have hcons : (vecCons (fun x => Real.log (h.dualNorm x)) fun (_ : Fin e) x =>
        Real.log (h.dualNorm x)) = fun _ x => Real.log (h.dualNorm x) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    rw [hcons] at hS
    rw [hS, hP, ← himg, finsum_mem_image hinj, finsum_mem_coe_finset]
    have hsum : ∑ W ∈ (divCycle J u).support,
        (localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
          (W ⊔ Ideal.span {linForm ℓ - 1}) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) :=
      Finset.sum_congr rfl fun W hW => by rw [hmult W hW]
    rw [hsum]
    ring
  have hlim := (tendsto_finsetSum _ fun W hW => (hlimW W hW).const_mul
    ((divCycle J u W : ℕ) : ℝ)).add herr
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hlimJ (hlim.congr hk)

end GroundTheory.Heights₂.Heights
