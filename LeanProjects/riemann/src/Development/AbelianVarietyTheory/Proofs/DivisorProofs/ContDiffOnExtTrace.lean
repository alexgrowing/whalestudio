import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem contDiffOn_extTrace : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H →
    ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  intro n m l _ _ _ _ U H hH ξ η
  have hM : ∀ v ∈ U, MContDiffAt ∞ H v := fun v hv a b =>
    (hH.smooth a b).contDiffAt (hH.isOpen.mem_nhds hv)
  have hP : ∀ v ∈ U, ∀ᶠ x in 𝓝 v, (H x).PosDef := fun v hv =>
    Filter.eventually_of_mem (hH.isOpen.mem_nhds hv) hH.posDef
  have key : ∀ v ∈ U,
      ContDiffAt ℝ ∞ (fun x => kappa * (secondForm H x ξ * secondFormAdj H x η).trace) v := by
    intro v hv
    have hu : IsUnit (H v).det := (hH.posDef v hv).det_pos.ne'.isUnit
    have hs : IsUnit (subGram (H v)).det := (posDef_subGram (hH.posDef v hv)).det_pos.ne'.isUnit
    have hc : ∀ ζ, MContDiffAt ∞ (fun x => secondForm H x ζ) v := fun ζ => by
      show MContDiffAt ∞ (fun x => quotMap m l * conn H x ζ * incl m l) v
      exact ((mContDiffAt_const _).mul ((hM v hv).conn hu (j := ∞) (by simp) ζ)).mul
        (mContDiffAt_const _)
    have ha : MContDiffAt ∞ (fun x => secondFormAdj H x η) v := by
      show MContDiffAt ∞ (fun x => (subGram (H x))ᵀ⁻¹ * (secondForm H x η)ᴴ * (quotGram (H x))ᵀ) v
      exact (((hM v hv).subGram.transpose.inv (by rwa [det_transpose])).mul
        (hc η).conjTranspose).mul ((hM v hv).quotGram hs).transpose
    have hp := (hc ξ).mul ha
    simp only [Matrix.trace, Matrix.diag_apply]
    exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => hp i i)
  intro v hv
  refine ((key v hv).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hH.isOpen.mem_nhds hv] with x hx
  exact extTrace_eq ((hM x hx).of_le (by simp)) (hP x hx) ξ η

end GlobalTheory.SecForm
