import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.SkewSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ (fun b => cc (y b)) := by
  unfold herm
  rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul]

theorem herm_sum_left {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G ((∑ i, c i • v i) *ᵥ u) w = ∑ i, c i * herm G (v i *ᵥ u) w := by
  simp only [herm_eq_dot, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.sum_vecMul,
    Matrix.smul_vecMul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem herm_sum_right {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G u ((∑ i, c i • v i) *ᵥ w) = ∑ i, cc (c i) * herm G u (v i *ᵥ w) := by
  have : (fun b => cc (((∑ i, c i • v i) *ᵥ w) b))
      = ∑ i, cc (c i) • (fun b => cc ((v i *ᵥ w) b)) := by
    funext b
    simp [cc, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply]
  simp only [herm_eq_dot, this, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (Y : Matrix (Fin r) (Fin r) E) (h : ∀ u w, herm G (Y *ᵥ u) w = 0) : Y = 0 := by
  have key : ∀ u, Y *ᵥ u = 0 := by
    intro u
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    have := h u (Pi.single b 1)
    rw [herm_eq_dot] at this
    have h2 : (fun b' => cc ((Pi.single b (1 : E) : Fin r → E) b')) = Pi.single b 1 := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [cc]
      · simp [cc, hb]
    rw [h2] at this
    simpa using this
  ext a b
  have := congrFun (key (Pi.single b 1)) a
  simpa using this

theorem linearIndependent_of_skew {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E)
    (hG : G.det ≠ 0) (v : ι → Matrix (Fin r) (Fin r) E)
    (hv : ∀ i u w, herm G (v i *ᵥ u) w + herm G u (v i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) v) : LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  have step : ∀ c : ι → E, ∑ i, c i • v i = 0 → ∀ i, c i + cc (c i) = 0 := by
    intro c hc
    have h1 : ∑ i, cc (c i) • v i = 0 := by
      apply eq_zero_of_herm G hG
      intro u w
      have h := herm_sum_right G c v u w
      rw [hc] at h
      have h0 : herm G u ((0 : Matrix (Fin r) (Fin r) E) *ᵥ w) = 0 := by simp [herm, cc]
      rw [h0] at h
      rw [herm_sum_left, ← neg_eq_zero, ← Finset.sum_neg_distrib, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eq_neg_of_add_eq_zero_right (hv i u w)]; ring
    have hm : ∀ i, c i + cc (c i) ∈ maximalRealSubfield E := by
      intro i
      rw [← IsCMField.complexConj_eq_self_iff]
      simp [cc, add_comm]
    intro i
    have := hli (fun i => ⟨c i + cc (c i), hm i⟩) (by
      have : ∑ i, (c i + cc (c i)) • v i = 0 := by
        simp only [add_smul, Finset.sum_add_distrib, hc, h1, add_zero]
      exact this) i
    exact congrArg Subtype.val this
  intro c hc j
  have h := step (fun i => cc (c j) * c i) (by
    simp only [mul_smul, ← Finset.smul_sum, hc, smul_zero]) j
  have h2 : 2 * (cc (c j) * c j) = 0 := by
    rw [← h]; simp [cc]; ring
  simp [cc] at h2
  exact h2

theorem finrank_ker_trace (K : Type) [Field K] (r : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) K K)) = (r + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin (r + 1)) K K)
  have hs : LinearMap.range (Matrix.traceLinearMap (Fin (r + 1)) K K) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨Matrix.single 0 0 a, by simp⟩
  rw [hs, finrank_top, Module.finrank_self, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  rw [sq]; omega

theorem mem_span_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  intro E _ _ _ r G e _ hG he hli X hX hXs
  rcases r with _ | r
  · have : X = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  by_contra hn
  have h1 : LinearIndependent (maximalRealSubfield E) (fun o : Option _ => Option.casesOn' o X e) :=
    hli.option hn
  have h2 := linearIndependent_of_skew G hG _ (by
    rintro (_ | i)
    · exact hXs
    · exact (he i).2) h1
  let f : Option (Fin ((r + 1) ^ 2 - 1)) →
      LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) E E) := fun o =>
    ⟨Option.casesOn' o X e, by
      rcases o with _ | i
      · exact hX
      · exact (he i).1⟩
  have h3 : LinearIndependent E f := LinearIndependent.of_comp (Submodule.subtype _) h2
  have h4 := h3.fintype_card_le_finrank
  rw [finrank_ker_trace] at h4
  simp at h4

end GlobalTheory.SkewSpan
