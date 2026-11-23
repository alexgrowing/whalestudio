import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private lemma prj_idem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  have h : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h

private lemma prj_comp_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj W ∘L prj V = prj V := by
  ext v
  have h1 : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  have h2 : prj V v ∈ W.topologicalClosure := Submodule.topologicalClosure_mono h h1
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h2

private lemma prj_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V := by
  have : IsSelfAdjoint (prj V) := by
    simpa [prj] using isSelfAdjoint_starProjection V.topologicalClosure
  exact this

private lemma prj_comp_le' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj V ∘L prj W = prj V := by
  have := congrArg ContinuousLinearMap.adjoint (prj_comp_le h)
  simpa [ContinuousLinearMap.adjoint_comp, prj_adj] using this

theorem UpperTheory.trOn_sub_sum_eq_trace_comp_compression :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (E : ℝ → Submodule ℂ H) (S : Finset ℝ) (a : ℝ → ℂ) (F T : H →L[ℂ] H), (∀ x, E x ≤ W) → IsTraceClass (prj W ∘L T ∘L prj W) → trOn W (F ∘L prj W ∘L T) - ∑ x ∈ S, a x * trOn (E x) T = trace ((prj W ∘L F ∘L prj W - ∑ x ∈ S, a x • prj (E x)) ∘L (prj W ∘L T ∘L prj W)) := by
  intro H _ _ _ W E S a F T hE hT
  set P := prj W with hPdef
  set T0 := P ∘L T ∘L P with hT0
  have hPP : P ∘L P = P := prj_idem W
  let L : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
    { toFun := fun C => trace (C ∘L T0)
      map_add' := fun C D => by
        rw [ContinuousLinearMap.add_comp]
        exact trace_add (hT.comp_left C) (hT.comp_left D)
      map_smul' := fun c C => by
        rw [ContinuousLinearMap.smul_comp]
        exact trace_smul c (hT.comp_left C) }
  have hL : ∀ C, L C = trace (C ∘L T0) := fun _ => rfl
  have h1 : trOn W (F ∘L P ∘L T) = L (P ∘L F ∘L P) := by
    rw [hL, trOn]
    congr 1
    have : (P ∘L F ∘L P) ∘L T0 = P ∘L F ∘L (P ∘L P) ∘L T ∘L P := by
      simp only [hT0, ContinuousLinearMap.comp_assoc]
    rw [this, hPP]
    simp only [hPdef, ContinuousLinearMap.comp_assoc]
  have h2 : ∀ x, trOn (E x) T = L (prj (E x)) := by
    intro x
    set Q := prj (E x) with hQ
    have hQP : Q ∘L P = Q := prj_comp_le' (hE x)
    have hPQ : P ∘L Q = Q := prj_comp_le (hE x)
    have hQQ : Q ∘L Q = Q := prj_idem (E x)
    have hc := trace_comp_comm (hT.comp_left Q) Q
    have e1 : Q ∘L (Q ∘L T0) = Q ∘L T0 := by
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have e2 : (Q ∘L T0) ∘L Q = Q ∘L T ∘L Q := by
      have : (Q ∘L T0) ∘L Q = (Q ∘L P) ∘L T ∘L (P ∘L Q) := by
        simp only [hT0, ContinuousLinearMap.comp_assoc]
      rw [this, hQP, hPQ]
    rw [e1, e2] at hc
    rw [hL, trOn, hc]
  rw [h1]
  simp only [h2]
  have h3 : L (P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) = trace ((P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) ∘L T0) := rfl
  rw [← h3, map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
