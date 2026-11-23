import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Mathlib.Analysis.Normed.Operator.Extend

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem gramExt {ι E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (a : ι → E) (b : ι → H)
    (hd : Dense ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E))
    (hg : ∀ i j, ⟪b i, b j⟫_ℂ = ⟪a i, a j⟫_ℂ) : ∃ J : E →ₗᵢ[ℂ] H, ∀ i, J (a i) = b i := by
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hden : DenseRange A := by
    have : Set.range A = ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E) := by
      rw [← Finsupp.range_linearCombination, LinearMap.coe_range]
    rw [DenseRange, this]; exact hd
  have hin : ∀ x y, ⟪B x, B y⟫_ℂ = ⟪A x, A y⟫_ℂ := by
    intro x y
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hg]
  have hn : ∀ x, ‖B x‖ = ‖A x‖ := by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  have hb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C * ‖A x‖ := ⟨1, fun x => by rw [one_mul, hn]⟩
  have h1 : ∀ x, (B.extendOfNorm A) (A x) = B x := fun x => LinearMap.extendOfNorm_eq hden hb x
  refine ⟨⟨(B.extendOfNorm A).toLinearMap, fun u => ?_⟩, fun i => ?_⟩
  · refine hden.induction_on (p := fun u => ‖(B.extendOfNorm A) u‖ = ‖u‖) u ?_ ?_
    · exact isClosed_eq (B.extendOfNorm A).continuous.norm continuous_norm
    · intro x; rw [h1, hn]
  · have := h1 (Finsupp.single i 1)
    simpa [A, B] using this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.isoExt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℕ) (T : (ℝ → ℂ) → Eu d → H),
      (∀ β β' v v', Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' → ⟪T β v, T β' v'⟫_ℂ = (∫ t, conj (β t) * β' t) * ⟪v, v'⟫_ℂ) →
      ∃ J : L (Eu d) →ₗᵢ[ℂ] H, ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) → J u = T β v := by
  intro H _ _ _ d T hT
  let ι := {p : (ℝ → ℂ) × Eu d × L (Eu d) //
    Continuous p.1 ∧ HasCompactSupport p.1 ∧ ∀ᵐ x : ℝ, p.2.2 x = p.1 x • p.2.1}
  obtain ⟨J, hJ⟩ := gramExt (ι := ι) (fun p => p.1.2.2) (fun p => T p.1.1 p.1.2.1) (by
    have h := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc d).1
    refine h.mono (SetLike.coe_subset_coe.2 (Submodule.span_mono ?_))
    rintro u ⟨β, v, h⟩
    exact ⟨⟨(β, v, u), h⟩, rfl⟩) (by
    rintro ⟨⟨β, v, u⟩, h1, h2, h3⟩ ⟨⟨β', v', u'⟩, h1', h2', h3'⟩
    dsimp only at *
    rw [hT β β' v v' h1 h2 h1' h2', MeasureTheory.L2.inner_def, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [h3, h3'] with x e e'
    rw [e, e', inner_smul_left, inner_smul_right, mul_assoc])
  exact ⟨J, fun β v u h1 h2 h3 => hJ ⟨(β, v, u), h1, h2, h3⟩⟩
