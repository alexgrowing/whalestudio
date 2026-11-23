import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem IsDerFam.hasDerivAt_exp {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {l : List (Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F l (z * NormedSpace.exp (t • X))) (F (X :: l) (z * NormedSpace.exp (s • X))) s := by
  have h1 := hF l hl X hX _ (mul_mem_UJ hz (exp_mem_UJ hX s))
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = F l (z * _ * _)
  rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem norm_sub_le_of_deriv_Icc {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s ∈ Set.Icc (-δ) δ, ‖f' s‖ ≤ B) {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) : ‖f t - f 0‖ ≤ B * |t| := by
  have := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hB (x := 0) (y := t) ⟨by linarith, hδ⟩ ht
  simpa using this

theorem domBy_derFam (n : ℕ) (ε : Fin n → Bool) (Z : Set (Mx n)) (C : ℝ) (N : ℕ) (F Φ : List (Mx n) → Mx n → ℂ)
    (g : Mx n) (hZ : IsCompact Z) (hZU : Z ⊆ UJset ε) (hC : 0 ≤ C) (hg : g ∈ UJset ε) (hF : IsDerFam ε F)
    (hG : FamGrowth ε N F) (hΦ : IsDerFam ε Φ) (h0 : DomBy ε Z C g (F []) (Φ [])) (l : List (Mx n))
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : DomBy ε Z C g (F l) (Φ l) := by
  induction l with
  | nil => exact h0
  | cons X l ih =>
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have ih := ih hl'
    intro ι _ a g' hg' M hM hb
    obtain ⟨C', hC'⟩ := hG (X :: X :: l) (by
      intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      exacts [hX, hl Y hY])
    have hmem : ∀ y ∈ Z, ∀ j, g * y * g' j ∈ UJset ε := fun y hy j => mul_mem_UJ (mul_mem_UJ hg (hZU hy)) (hg' j)
    have hcont : Continuous fun p : Mx n × ℝ =>
        ∑ j, ‖a j‖ * (C' * (1 + hs (g * p.1 * g' j * NormedSpace.exp (p.2 • X))) ^ N) := by
      refine continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_const.mul
        ((continuous_const.add (continuous_hs.comp ?_)).pow _))
      exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).matrix_mul
        ((continuous_exp_smul X).comp continuous_snd)
    obtain ⟨K₀, hK₀⟩ := (hZ.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).bddAbove_image hcont.continuousOn
    set K := max K₀ 0 with hK
    have hK0 : 0 ≤ K := le_max_right _ _
    have h2 : ∀ y ∈ Z, ∀ s ∈ Set.Icc (-1 : ℝ) 1,
        ‖∑ j, a j * F (X :: X :: l) (g * y * g' j * NormedSpace.exp (s • X))‖ ≤ K := by
      intro y hy s hs'
      refine (norm_sum_le _ _).trans (le_trans ?_ ((hK₀ ⟨(y, s), ⟨hy, hs'⟩, rfl⟩).trans (le_max_left _ _)))
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC' _ (mul_mem_UJ (hmem y hy j) (exp_mem_UJ hX s))) (norm_nonneg _)
    have e0 : NormedSpace.exp ((0 : ℝ) • X) = 1 := by rw [zero_smul, NormedSpace.exp_zero]
    have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖∑ j, a j * Φ (X :: l) (g' j)‖ ≤ C * (M + K * δ) := by
      intro δ hδ hδ1
      have h1 : ∀ y ∈ Z, ∀ s ∈ Set.Icc (-δ) δ,
          ‖∑ j, a j * F (X :: l) (g * y * g' j * NormedSpace.exp (s • X))‖ ≤ M + K * δ := by
        intro y hy s hs'
        have h := norm_sub_le_of_deriv_Icc
          (f := fun t => ∑ j, a j * F (X :: l) (g * y * g' j * NormedSpace.exp (t • X)))
          (fun s => HasDerivAt.fun_sum fun j _ => (hF.hasDerivAt_exp hl hX (hmem y hy j) s).const_mul (a j))
          zero_le_one (h2 y hy) (t := s) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
        simp only [e0, Matrix.mul_one] at h
        have h' : K * |s| ≤ K * δ := mul_le_mul_of_nonneg_left (abs_le.2 hs') hK0
        have := norm_le_norm_add_norm_sub' (∑ j, a j * F (X :: l) (g * y * g' j * NormedSpace.exp (s • X)))
          (∑ j, a j * F (X :: l) (g * y * g' j))
        linarith [hb y hy]
      have hψ : HasDerivAt (fun t : ℝ => ∑ j, a j * Φ l (g' j * NormedSpace.exp (t • X)))
          (∑ j, a j * Φ (X :: l) (g' j)) 0 :=
        HasDerivAt.fun_sum fun j _ => (hΦ l hl' X hX _ (hg' j)).const_mul (a j)
      have hMK : 0 ≤ M + K * δ := by positivity
      refine hψ.le_of_lip' (by positivity) ?_
      filter_upwards [Icc_mem_nhds (a := -δ) (b := δ) (x := (0 : ℝ)) (by linarith) hδ] with t ht
      have h := ih (ι ⊕ ι) (Sum.elim a fun j => -a j) (Sum.elim (fun j => g' j * NormedSpace.exp (t • X)) g')
        (by
          rintro (j | j)
          exacts [mul_mem_UJ (hg' j) (exp_mem_UJ hX t), hg' j]) ((M + K * δ) * |t|) (by positivity) (by
          intro y hy
          have h := norm_sub_le_of_deriv_Icc
            (f := fun t => ∑ j, a j * F l (g * y * g' j * NormedSpace.exp (t • X)))
            (fun s => HasDerivAt.fun_sum fun j _ => (hF.hasDerivAt_exp hl' hX (hmem y hy j) s).const_mul (a j))
            hδ.le (h1 y hy) ht
          simpa only [e0, Matrix.mul_one, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul,
            Finset.sum_neg_distrib, ← sub_eq_add_neg, Matrix.mul_assoc] using h)
      simpa only [e0, Matrix.mul_one, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul,
        Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_zero, Real.norm_eq_abs, mul_assoc] using h
    have hlim : Tendsto (fun δ : ℝ => C * (M + K * δ)) (𝓝[>] 0) (𝓝 (C * M)) := by
      have hc : Continuous fun δ : ℝ => C * (M + K * δ) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
    exact key δ hδ.1 hδ.2

end GlobalTheory.TypeSum
