import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem sobNorm_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S A : List (List (Mx n))) (w : H) :
    sobNorm σ (S ++ A) w = sobNorm σ S w + sobNorm σ A w := by
  simp [sobNorm, List.map_append, List.sum_append]

private theorem sobNorm_nonneg' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S : List (List (Mx n))) (w : H) : 0 ≤ sobNorm σ S w := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

private theorem exists_sobNorm_bound_of_sobBdOn_continuous_seminorm {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (σ : Mx n → H →L[ℂ] H) (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p) (T : H →ₗ[ℂ] E)
    (hT : SobBdOn ε σ (Sm ε σ) p T) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → q (T w) ≤ C * sobNorm σ S w := by
  have key : ∀ s : Finset ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → ∑ j ∈ s, p j (T w) ≤ C * sobNorm σ S w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨[], 0, fun l hl => by simp at hl, le_rfl, fun w _ => by simp⟩
    | insert j s hj ih =>
      obtain ⟨S, C, hS, hC, hb⟩ := ih
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hT j
      refine ⟨S₁ ++ S, max C₁ 0 + C, ?_, by positivity, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · exact hS₁ l h
        · exact hS l h
      · intro w hw
        rw [Finset.sum_insert hj, sobNorm_append']
        have h1 := hb₁ w hw
        have h2 := hb w hw
        have n1 := sobNorm_nonneg' σ S₁ w
        have n2 := sobNorm_nonneg' σ S w
        have h3 : C₁ * sobNorm σ S₁ w ≤ max C₁ 0 * sobNorm σ S₁ w :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC n1]
  obtain ⟨s, C0, -, hle⟩ := Seminorm.bound_of_continuous hp q hq
  obtain ⟨S, C, hS, hC, hb⟩ := key s
  refine ⟨S, C0 * C, hS, mul_nonneg C0.2 hC, fun w hw => ?_⟩
  have hsup : (s.sup p) (T w) ≤ ∑ j ∈ s, p j (T w) :=
    Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      (fun i hi => Finset.single_le_sum (f := fun j => p j (T w)) (fun _ _ => apply_nonneg _ _) hi)
  calc q (T w) ≤ (C0 • s.sup p) (T w) := Seminorm.le_def.1 hle (T w)
    _ = (C0 : ℝ) * (s.sup p) (T w) := by rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ (C0 : ℝ) * ∑ j ∈ s, p j (T w) := mul_le_mul_of_nonneg_left hsup C0.2
    _ ≤ (C0 : ℝ) * (C * sobNorm σ S w) := mul_le_mul_of_nonneg_left (hb w hw) C0.2
    _ = C0 * C * sobNorm σ S w := by ring

theorem d3 : D3 := by
  intro hD0 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hDens T hT hSob w hw
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hU
  have hp := hπ.withSeminorms
  constructor
  · intro k hk
    have hkU : k ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) := by
      show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
      have h1 : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
      rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose, h1, one_mul]
    have hkUJ : k ∈ UJset ε := hkU
    let T' : H →ₗ[ℂ] E := T ∘ₗ (σ k).toLinearMap - (π k).toLinearMap ∘ₗ T
    have hT' : ∀ v, T' v = T (σ k v) - π k (T v) := fun _ => rfl
    have hsob : SobBdOn ε σ (Sm ε σ) p T' := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (π k).toLinearMap)
        ((hp.continuous_seminorm i).comp (π k).continuous)
      refine ⟨S₁.map (List.map fun X => k⁻¹ * X * k) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
          exact conj_mem_lie hJu hkU (hS₁ l' hl' X hX)
        · exact hS₂ l h
      · intro v hv
        have hsv : σ k v ∈ smooth (Formalism.REAL.Jm ε) σ := translate_mem hJu hU' hkU hv
        have heq : sobNorm σ S₁ (σ k v) =
            sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l hl
          simp only [Function.comp_apply]
          rw [word_translate hJu hU' hkU hv l (fun X hX => hS₁ l hl X hX), hU.2.1 k hkUJ,
            List.foldr_map]
        have h1 := hb₁ (σ k v) hsv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hT', sobNorm_append']
        have h3 : (p i) (T (σ k v) - π k (T v)) ≤ p i (T (σ k v)) + p i (π k (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (π k).toLinearMap) (T v) = p i (π k (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens T' hsob
      (fun v hv => by rw [hT', hT.1 k hk v hv, sub_self]) w hw
    rw [hT'] at h0
    exact sub_eq_zero.1 h0
  · intro X hX
    obtain ⟨L, hL⟩ := exists_word hJu hU' [X] (fun Y hY => by
      rw [List.mem_singleton] at hY
      rw [hY]
      exact hX)
    let f : smooth (Formalism.REAL.Jm ε) σ →ₗ[ℂ] E :=
      T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype ∘ₗ L -
        (dπ X).toLinearMap ∘ₗ T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    have hgw : ∀ v (hv : Sm ε σ v), g v = T (dRep σ X v) - dπ X (T v) := by
      intro v hv
      have h := LinearMap.congr_fun hg ⟨v, hv⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
      rw [h]
      simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply, hL,
        List.foldr_cons, List.foldr_nil, ContinuousLinearMap.coe_coe]
    have hsob : SobBdOn ε σ (Sm ε σ) p g := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (dπ X).toLinearMap)
        ((hp.continuous_seminorm i).comp (dπ X).continuous)
      refine ⟨S₁.map (fun l => l ++ [X]) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          rcases List.mem_append.1 hY with h' | h'
          · exact hS₁ l' hl' Y h'
          · rw [List.mem_singleton.1 h']
            exact hX
        · exact hS₂ l h
      · intro v hv
        have hdv : Sm ε σ (dRep σ X v) := dRep_mem hJu hU' hv hX
        have heq : sobNorm σ S₁ (dRep σ X v) = sobNorm σ (S₁.map (fun l => l ++ [X])) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l _
          simp [List.foldr_append]
        have h1 := hb₁ (dRep σ X v) hdv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (fun l => l ++ [X])) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hgw v hv, sobNorm_append']
        have h3 : (p i) (T (dRep σ X v) - dπ X (T v)) ≤ p i (T (dRep σ X v)) + p i (dπ X (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (dπ X).toLinearMap) (T v) = p i (dπ X (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (fun l => l ++ [X])) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (fun l => l ++ [X])) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens g hsob
      (fun v hv => by rw [hgw v (hDens.1 v hv), hT.2 X hX v hv, sub_self]) w hw
    rw [hgw w hw] at h0
    exact sub_eq_zero.1 h0

end PositivityTheory.CW

end
