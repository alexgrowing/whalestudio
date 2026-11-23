import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace PositivityTheory.CW.SeminormApproximation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem sup_bound {p : ℕ → Seminorm ℂ E} {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (s : Finset ℕ) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → s.sup p (T x) ≤ C * sobNorm σ S x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨[], 0, fun l hl => by simp at hl, le_refl _, fun x _ => ?_⟩
    simp [Seminorm.bot_eq_zero]
  · intro i s _ ih
    obtain ⟨S, C, hS, hC, h⟩ := ih
    obtain ⟨S', C', hS', h'⟩ := hT i
    refine ⟨S' ++ S, |C'| + C, words_append hS' hS, by positivity, fun x hx => ?_⟩
    rw [Finset.sup_insert, Seminorm.sup_apply, sobNorm_append]
    have e1 := h x hx
    have e2 := h' x hx
    have a := sobNorm_nonneg σ S x
    have b := sobNorm_nonneg σ S' x
    have c1 := mul_nonneg (abs_nonneg C') a
    have c2 := mul_nonneg hC b
    have c3 := mul_nonneg hC a
    have c4 := mul_nonneg (abs_nonneg C') b
    have c5 := mul_le_mul_of_nonneg_right (le_abs_self C') b
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith

theorem q_bound {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → Q (T x) ≤ C * sobNorm σ S x := by
  obtain ⟨s, C', -, hle⟩ := Seminorm.bound_of_continuous hp Q hQ
  obtain ⟨S, C, hS, hC, h⟩ := sup_bound hT s
  refine ⟨S, C' * C, hS, mul_nonneg (NNReal.coe_nonneg C') hC, fun x hx => ?_⟩
  have h1 : Q (T x) ≤ (C' • s.sup p) (T x) := hle (T x)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
  calc Q (T x) ≤ C' * s.sup p (T x) := h1
    _ ≤ C' * (C * sobNorm σ S x) := mul_le_mul_of_nonneg_left (h x hx) (NNReal.coe_nonneg C')
    _ = _ := by ring

theorem approx (hD : Dens ε σ) {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p)
    {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (y : H) (hy : Sm ε σ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v, IsKFin ε σ v ∧ Q (T (y - v)) ≤ δ ∧ ‖y - v‖ ≤ δ ∧ ‖Dw σ l (y - v)‖ ≤ δ := by
  obtain ⟨S, C, hS, hC, h⟩ := q_bound hp hT Q hQ
  have hW : Words (lieSet ε) (S ++ [l, []]) := by
    intro m hm X hX
    rcases List.mem_append.1 hm with hm | hm
    · exact hS m hm X hX
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hl X hX
      · simp at hX
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hlt⟩ := hD.2.2 y hy (S ++ [l, []]) hW (δ / (C + 1)) (div_pos hδ hC1)
  have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
  have e : sobNorm σ (S ++ [l, []]) (y - v) = sobNorm σ S (y - v) + (‖Dw σ l (y - v)‖ + ‖y - v‖) := by
    rw [sobNorm_append]
    congr 1
    simp [sobNorm]
  rw [e] at hlt
  have a := sobNorm_nonneg σ S (y - v)
  have n1 := norm_nonneg (Dw σ l (y - v))
  have n2 := norm_nonneg (y - v)
  have hρ : δ / (C + 1) ≤ δ := div_le_self hδ.le (by linarith)
  have hCρ : C * (δ / (C + 1)) ≤ δ := by
    have : (C + 1) * (δ / (C + 1)) = δ := by field_simp
    nlinarith [div_pos hδ hC1]
  refine ⟨v, hv, ?_, by linarith, by linarith⟩
  calc Q (T (y - v)) ≤ C * sobNorm σ S (y - v) := h _ hsm
    _ ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ δ := hCρ

end PositivityTheory.CW.SeminormApproximation

namespace PositivityTheory.CW

open SeminormApproximation in
theorem e2d : SobolevBoundedPairing := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT Q hQ l η C hl
  have hp := hπ.withSeminorms
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · refine le_of_forall_pos_le_add fun e he => ?_
    have hK : 0 < |C| + ‖η‖ + 1 := by positivity
    obtain ⟨v, hv, h1, h2, -⟩ := approx hD hp hT Q hQ l hl y hy (e / (|C| + ‖η‖ + 1)) (div_pos he hK)
    have hv' := h v hv
    have i1 : ‖⟪η, y⟫_ℂ‖ ≤ ‖⟪η, v⟫_ℂ‖ + ‖η‖ * ‖y - v‖ := by
      have : ⟪η, y⟫_ℂ = ⟪η, v⟫_ℂ + ⟪η, y - v⟫_ℂ := by rw [inner_sub_right]; ring
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_inner_le_norm _ _))
    have i2 : |Q (T v) - Q (T y)| ≤ Q (T (y - v)) := by
      rw [show T (y - v) = T y - T v from map_sub T y v, abs_sub_comm]
      exact abs_sub_map_le_sub Q (T y) (T v)
    have i3 : C * (Q (T v) - Q (T y)) ≤ |C| * Q (T (y - v)) := by
      have := le_abs_self (C * (Q (T v) - Q (T y)))
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left i2 (abs_nonneg C))
    have i4 : C * Q (T v) = C * Q (T y) + C * (Q (T v) - Q (T y)) := by ring
    have i5 : |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖ ≤ e := by
      calc |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖
          ≤ |C| * (e / (|C| + ‖η‖ + 1)) + ‖η‖ * (e / (|C| + ‖η‖ + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ = (|C| + ‖η‖) * (e / (|C| + ‖η‖ + 1)) := by ring
        _ ≤ (|C| + ‖η‖ + 1) * (e / (|C| + ‖η‖ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_pos he hK).le
        _ = e := by field_simp
    linarith
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨v, hv, h1, -, h3⟩ := approx hD hp hT Q hQ l hl y hy (e / 2) (by positivity)
    have hv' := h v hv
    have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
    have hsplit : Dw σ l y = Dw σ l (y - v) + Dw σ l v := by
      have := Dw_add hU hl hsm (hD.1 v hv)
      rwa [sub_add_cancel] at this
    have i1 : ‖Dw σ l y‖ ≤ ‖Dw σ l (y - v)‖ + ‖Dw σ l v‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have i2 : Q (T v) ≤ Q (T y) + Q (T (y - v)) := by
      have := map_sub_le_add Q (T y) (T (y - v))
      have e2 : T y - T (y - v) = T v := by rw [map_sub T y v, sub_sub_cancel]
      rwa [e2] at this
    linarith

end PositivityTheory.CW

end
