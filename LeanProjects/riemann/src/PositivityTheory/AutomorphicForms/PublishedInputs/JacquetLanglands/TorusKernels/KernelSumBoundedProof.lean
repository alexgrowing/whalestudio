import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace UpperTheory.Esk

namespace KernelSumBound

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num) h.le) (by positivity)
  · exact le_rfl

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w := by
  unfold Kap
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

theorem bound (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (C₀ : ℝ)
    (hk : ∀ (γ : PG F) (y : D.Y), ‖D.kk k a γ y‖ ≤ C₀ * Kap k y.2 (γ • y.2 : D.Xs))
    (hsupp : ∀ (γ : PG F) (ω : D.Om), D.Te a γ.out (D.rep ω) ≠ 0 →
      ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H))
    (y : D.Y) (B : ℝ)
    (hB : ∀ ω' : D.Om, ∑' γ : {γ : PG F // γ • y.1 = ω'},
      ENNReal.ofReal (Kap k y.2 (γ.1 • y.2 : D.Xs)) ≤ ENNReal.ofReal B) :
    ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
  classical
  have hpt : ∀ γ : PG F, ‖D.kk k a γ y‖ₑ ≤ ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := by
    intro γ
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have hz : D.kk k a γ y = 0 := by
        simp only [Dat.kk, Dat.kt, h0, zero_mul]
      rw [hz, enorm_zero]
      exact zero_le
    · obtain ⟨i, hi⟩ := hsupp γ y.1 h0
      calc ‖D.kk k a γ y‖ₑ = ENNReal.ofReal ‖D.kk k a γ y‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (C₀ * Kap k y.2 (γ • y.2 : D.Xs)) := ENNReal.ofReal_le_ofReal (hk γ y)
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)) :=
            ENNReal.ofReal_mul' (Kap_nonneg k _ _)
        _ = Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
            (Set.indicator_of_mem
              (show γ ∈ {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)
              (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)))).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a j : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ)
            (fun _ _ => zero_le) (Finset.mem_univ i)
  have hsub : ∀ i : ι, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal B := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    exact hB ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)
  calc ∑' γ : PG F, ‖D.kk k a γ y‖ₑ
      ≤ ∑' γ : PG F, ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑ i, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : ι, ENNReal.ofReal C₀ * ENNReal.ofReal B := Finset.sum_le_sum fun i _ => hsub i
    _ = Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end KernelSumBound

end UpperTheory.Esk

theorem UpperTheory.Esk.kernel_sum_bounded_proof : UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.E2 := by
  intro h0c h0d hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨-, -, -, ⟨C₀, hC₀⟩, hsupp, -⟩ := h0c F I Gf ι D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, -⟩ := h0d F I Gf D hyp.ax
  have key : ∀ T : ℝ, ∀ y ∈ D.abelian₂ T, ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≤
      Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal (max C 0 * (1 + T))) := by
    intro T y hy
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hpos : 0 < D.HtY s y := lt_of_lt_of_le hc₀ hcs
    have hle : D.HtY s y ≤ T := hy s hs
    refine UpperTheory.Esk.KernelSumBound.bound D k a C₀ hC₀ hsupp y (max C 0 * (1 + T)) fun ω' => ?_
    refine (hC y s hs hcs ω' y.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left C 0) (by linarith) (by linarith) (le_max_right C 0)
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal), fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := hT y
    have hfin : ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) (key T₀ y (hT₀ T₀ le_rfl))
    exact (ENNReal.summable_toReal hfin).congr fun γ => toReal_enorm _
  · refine (key T y hy).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
    all_goals rfl
