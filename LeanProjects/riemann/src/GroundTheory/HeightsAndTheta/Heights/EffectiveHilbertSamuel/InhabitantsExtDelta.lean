import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.InhabitantsExt
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtTwist
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtShell
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCutoff
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open ExtInhabitants

theorem extTwist_hyp : ∃ (X : EmbDatum 1) (Z : ZeroDatum X), 1 ≤ 1 ∧ 2 ≤ 2 ∧ Z.S.Nonempty ∧
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 :=
  let ⟨X, Z, h1, h2, h3⟩ := extDelta_hyp
  ⟨X, Z, h1, h2, h3, one_pos, one_pos⟩

theorem extShell_hyp : IsOpen (univ : Set exEmb.U) ∧ exZ.S ⊆ univ ∧
    (∀ k, ContinuousOn (exOne k ∘ (exEmb.A.chart k).symm)
      ((exEmb.A.chart k).target ∩ (exEmb.A.chart k).symm ⁻¹' univ)) ∧
    (∀ k l, ∀ x ∈ (exEmb.A.chart k).source ∩ (exEmb.A.chart l).source ∩ univ,
      exOne k x = jac exEmb.A k l x * exEmb.L₂.g k l x * exEmb.L.g k l x ^ (1 + 2) * exOne l x) ∧
    (∀ x ∈ exZ.S, exOne (chartIdx exEmb.A x) x =
      (fun _ => (1 : ℂ)) x * sJac exEmb.A exZ.s (chartIdx exEmb.A x) x) ∧ exZ.S.Nonempty := by
  refine ⟨isOpen_univ, subset_univ _, fun k => continuousOn_const, fun k l x _ => ?_,
    fun x _ => ?_, ?_⟩
  · simp [exOne, jac_flat, trivLB]
  · change (1 : ℂ) = 1 * sJac (flatAtlas 1) (fun i => lin exE (exC i)) _ x
    rw [exSJac, one_mul]
  · obtain ⟨X, Z, -, -, h⟩ := extDelta_hyp
    exact ⟨0, by
      change (0 : Fin 1 → ℂ) ∈ zeroSet (flatAtlas 1) (fun i => lin exE (exC i))
      rw [exZero]; rfl⟩

theorem bergmanProj_hyp :
    (∀ k, ContinuousOn (exEmb.wt 2 k ∘ (exEmb.A.chart k).symm) (exEmb.A.chart k).target) ∧
    (∀ k l, ∀ x ∈ (exEmb.A.chart k).source ∩ (exEmb.A.chart l).source,
      exEmb.wt 2 k x = exEmb.wt 2 l x + Real.log (‖exEmb.L₂.g k l x * exEmb.L.g k l x ^ 2‖ ^ 2)) ∧
    (∀ k, ContinuousOn (exOne k ∘ (exEmb.A.chart k).symm) (exEmb.A.chart k).target) ∧
    (∀ k l, ∀ x ∈ (exEmb.A.chart k).source ∩ (exEmb.A.chart l).source,
      exOne k x = jac exEmb.A k l x * exEmb.L₂.g k l x * exEmb.L.g k l x ^ 2 * exOne l x) ∧
    topNormSq exEmb.A (exEmb.wt 2) exOne < ⊤ ∧ exOne ≠ 0 := by
  refine ⟨fun k => ?_, fun k l x _ => ?_, fun k => continuousOn_const,
    fun k l x _ => by simp [exOne, jac_flat, trivLB], ?_, fun h => ?_⟩
  · apply Continuous.continuousOn
    have h1 : ∀ y, (∑ i : Fin 1, ‖exE₂ i k y‖ ^ 2) = 1 := fun y => by simp [exE₂]
    have h2 : ∀ y, (∑ i : Fin 2, ‖exE i k y‖ ^ 2) = 1 + ‖y 0‖ ^ 2 := fun y => by
      simp [exE, Fin.sum_univ_two]
    have e : exEmb.wt 2 k ∘ (exEmb.A.chart k).symm =
        fun y => Real.log 1 + ((2 : ℕ) : ℝ) * Real.log (1 + ‖y 0‖ ^ 2) := by
      funext y
      change Real.log (∑ i : Fin 1, ‖exE₂ i k y‖ ^ 2) +
        ((2 : ℕ) : ℝ) * Real.log (∑ i : Fin 2, ‖exE i k y‖ ^ 2) = _
      rw [h1, h2]
    rw [e]
    exact continuous_const.add (continuous_const.mul
      ((continuous_const.add ((continuous_apply 0).norm.pow 2)).log fun y =>
        (by positivity : (0 : ℝ) < 1 + ‖y 0‖ ^ 2).ne'))
  · have hkl : k = l := Subsingleton.elim k l
    subst hkl
    simp [trivLB]
  · change chartIntegral (flatAtlas 1) _ < ⊤
    rw [chartIntegral_flat]
    simp only [exOne, norm_one, one_pow, mul_one]
    simp only [exp_neg_wt]
    simpa using lintegral_inv_one_add_sq_sq_lt_top 2
  · have := congr_fun (congr_fun h c0) 0
    simp [exOne] at this

end

end GroundTheory.Heights₂.Heights.EffectiveHS
