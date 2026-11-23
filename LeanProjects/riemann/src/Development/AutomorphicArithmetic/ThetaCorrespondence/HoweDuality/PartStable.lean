import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.partStable :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (K : Submodule ℂ (M i)), (∀ g : Module.End ℂ M₀, ∀ t ∈ part M₀ i K, TensorProduct.map g LinearMap.id t ∈ part M₀ i K) ∧ (∀ g : Module.End ℂ (M i), (∀ x ∈ K, g x ∈ K) → ∀ t ∈ part M₀ i K, factorOp i g t ∈ part M₀ i K) ∧ ∀ l, l ≠ i → ∀ g : Module.End ℂ (M l), ∀ t ∈ part M₀ i K, factorOp l g t ∈ part M₀ i K := by
  intro ι _ _ M₀ _ _ M _ _ i K
  have mem : ∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K, intersection_update_fsHerm_neg_one i r x ∈ part M₀ i K := fun r x hx =>
    (le_iSup (fun r : M₀ × ∀ j, M j => K.map (intersection_update_fsHerm_neg_one i r)) r) (Submodule.mem_map_of_mem hx)
  have key : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K, Φ (intersection_update_fsHerm_neg_one i r x) ∈ part M₀ i K) →
      ∀ t ∈ part M₀ i K, Φ t ∈ part M₀ i K := by
    intro Φ h t ht
    have : part M₀ i K ≤ (part M₀ i K).comap Φ :=
      iSup_le fun r => Submodule.map_le_iff_le_comap.2 fun x hx => h r x hx
    exact this ht
  refine ⟨fun g => key _ fun r x hx => ?_, fun g hg => key _ fun r x hx => ?_,
    fun l hl g => key _ fun r x hx => ?_⟩
  · have := mem (g r.1, r.2) x hx
    simpa [position_apply] using this
  · have := mem r (g x) (hg x hx)
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    · rfl
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · have := mem (r.1, Function.update r.2 l (g (r.2 l))) x hx
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    · rfl
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_of_ne hl.symm]
    · by_cases hj' : j = l
      · subst hj'; simp [Function.update_of_ne hj]
      · simp [Function.update_of_ne hj, Function.update_of_ne hj']
