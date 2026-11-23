import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegVarBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutTailMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

theorem SliceRegTail.exists_bound {n : ℕ} {a : (Fin n → ℂ) → ℝ}
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |a x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (hac.mono fun x hx => ne_zero_of_mem_unit_sphere ⟨x, hx⟩)
  refine ⟨max C₀ |a 0| + 1, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; linarith [le_max_right C₀ |a 0|]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    have hy : (‖x‖ : ℂ)⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have := hC₀ _ hy
    rw [Real.norm_eq_abs, ← ha (‖x‖ : ℂ) _ hn, smul_inv_smul₀ hn] at this
    linarith [le_max_left C₀ |a 0|]

theorem SliceRegTail.proof (hB : SliceRegVarBound.Statement) (hT : SliceRegTailMass.Statement)
    (hM : SliceCutTailMass.Statement) : SliceRegTail.Statement := by
  intro n e h W F u' ℓ a hW hF hu hℓ hℓP ha hac δ hδ
  obtain ⟨C, hC0, hC⟩ := SliceRegTail.exists_bound ha hac
  have hδ' : 0 < δ / (3 * C) := by positivity
  obtain ⟨K₁, hK₁⟩ := hT n e h W F u' ℓ hW hF hu hℓ hℓP _ hδ'
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const hδ' (hM n e h W F ℓ hW hF hℓ))
  refine ⟨max K₁ K₂, fun k hk ε hε => ?_⟩
  have hma : Measurable a := measurable_of_continuousOn_compl_singleton 0 hac
  have hI := SliceCut.mem_Icc h k
  have hb := hB n e h W F u' ℓ ε C a (fun x => sliceCut h k x * a x) (fun x => 1 - sliceCut h k x)
    hW hF hℓ hε.1 hma ((SliceCut.measurable h k).mul hma) (measurable_const.sub (SliceCut.measurable h k)) hC
    (fun x => by
      rw [abs_mul, abs_of_nonneg (hI x).1]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
    (fun x => ⟨by linarith [(hI x).2], by linarith [(hI x).1]⟩)
    (fun x => by
      rw [show a x - sliceCut h k x * a x = (1 - sliceCut h k x) * a x by ring, abs_mul,
        abs_of_nonneg (by linarith [(hI x).2] : (0 : ℝ) ≤ 1 - sliceCut h k x)]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
  have h1 := hK₁ k (le_of_max_le_left hk) ε hε
  have h2 := hK₂ k (le_of_max_le_right hk)
  refine hb.trans ?_
  have h3 : C * (δ / (3 * C)) = δ / 3 := by field_simp
  nlinarith

end GroundTheory.Heights₂.Heights
