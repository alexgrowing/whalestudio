import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma sq_sum_le_of_dom (π : Equiv.Perm (Fin (2 + 2))) (μ ν : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν i ^ 2 ≤ ∑ i, μ i ^ 2 := by
  have hm : Monotone ((fun i => -ν i) ∘ Tuple.sort (fun i => -ν i)) := Tuple.monotone_sort _
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (2 + 2)), Monotone ((fun i => -ν i) ∘ τ) := ⟨_, hm⟩
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (2 + 2)), s = τ * π⁻¹ := ⟨_, rfl⟩
  have hanti : Antitone ((fun i => ν (s i)) ∘ π) := by
    intro a b hab
    have := hτ hab
    simp only [Function.comp, neg_le_neg_iff] at this
    simpa [hs, Equiv.Perm.mul_apply] using this
  have h1 := h s⁻¹ (fun i => ν (s i)) hanti
  have h2 : ∑ i, ν i * ν (s (s⁻¹ i)) = ∑ i, ν i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  rw [h2] at h1
  have h3 : ∑ i, ν (s i) ^ 2 = ∑ i, ν i ^ 2 := Equiv.sum_comp s fun i => ν i ^ 2
  have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ μ fun i => ν (s i)
  rw [h3] at h4
  have hA : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨A, hAe⟩ : ∃ A, A = ∑ i, ν i ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBe⟩ : ∃ B, B = ∑ i, μ i ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hCe⟩ : ∃ C, C = ∑ i, μ i * ν (s i) := ⟨_, rfl⟩
  rw [← hAe, ← hCe] at h1
  rw [← hAe, ← hBe, ← hCe] at h4
  rw [← hAe] at hA
  rw [← hBe] at hB
  rw [← hAe, ← hBe]
  rcases hA.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · have h5 : A * A ≤ B * A := by nlinarith
    exact le_of_mul_le_mul_right h5 h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expNorm :
    ∀ π ψ μ, OExp π ψ μ → WExp ψ μ := by
  intro π ψ μ h
  obtain ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩ := h
  refine ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, fun j => sq_sum_le_of_dom π μ (ν j) (hg j), ?_⟩
  intro j hj hEq
  have := hg' j hj
  rw [hEq] at this
  exact lt_irrefl _ this
