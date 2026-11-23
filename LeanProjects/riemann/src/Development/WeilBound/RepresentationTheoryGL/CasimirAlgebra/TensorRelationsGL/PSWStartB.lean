import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStartA

noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem dense [CompactSpace Γ] [T2Space Γ] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    (g : C(Γ, ℂ)) : g ∈ closure {h : C(Γ, ℂ) | ⇑h ∈ Submodule.span ℂ (Mono κ H)} := by
  let S : Set C(Γ, ℂ) := {g | ∃ τ i j, (g : Γ → ℂ) = fun k => κ τ k i j}
  let A : StarSubalgebra ℂ C(Γ, ℂ) := StarAlgebra.adjoin ℂ S
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨τ, hτ⟩ : ∃ τ, κ τ x ≠ κ τ y := by
      by_contra h
      push Not at h
      exact hxy (hK.sep x y h)
    obtain ⟨i, j, hij⟩ : ∃ i j, κ τ x i j ≠ κ τ y i j := by
      by_contra h
      push Not at h
      exact hτ (Matrix.ext h)
    exact ⟨fun k => κ τ k i j, ⟨⟨fun k => κ τ k i j, hK.cont τ i j⟩,
      StarAlgebra.subset_adjoin ℂ S ⟨τ, i, j, rfl⟩, rfl⟩, hij⟩
  have hsub : A.toSubalgebra ≤ (monoAlg hK H).comap (ContinuousMap.coeFnAlgHom ℂ) := by
    rw [StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro g (hg | hg)
    · obtain ⟨τ, i, j, hg⟩ := hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      rw [hg]
      exact entry_mem hK hH τ i j
    · obtain ⟨τ, i, j, hg⟩ := Set.mem_star.1 hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      have : (g : Γ → ℂ) = fun k => κ (bar τ) k i j := by
        funext k
        have h1 := congrFun hg k
        simp only [ContinuousMap.star_apply] at h1
        rw [hK.conj, ← h1, star_star]
      rw [this]
      exact entry_mem hK hH (bar τ) i j
  have hle : ∀ h ∈ A, ⇑h ∈ Submodule.span ℂ (Mono κ H) := fun h hh => hsub hh
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hg : g ∈ A.topologicalClosure := by rw [htop]; exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hg
  exact closure_mono (fun h hh => hle h hh) hg

theorem nonvanish [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] [T2Space Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    {f : Γ → ℂ} (hf : Continuous f) (x : Γ) (hx : f x ≠ 0) : ∃ g ∈ Mono κ H, ∫ k, g k * f k ∂μ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hspan : ∀ g ∈ Submodule.span ℂ (Mono κ H), Continuous g ∧ ∫ k, g k * f k ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hcon g hg⟩
      obtain ⟨m, lab, c, I, K, -, rfl⟩ := hg
      exact mono_cont hK lab c I K
    | zero => exact ⟨continuous_const, by simp⟩
    | add g g' _ _ h h' =>
      refine ⟨h.1.add h'.1, ?_⟩
      simp only [Pi.add_apply, add_mul]
      rw [integral_add (integrable_of_cont μ (f := fun k => g k * f k) (h.1.mul hf))
        (integrable_of_cont μ (f := fun k => g' k * f k) (h'.1.mul hf)), h.2, h'.2,
        add_zero]
    | smul a g _ h =>
      refine ⟨h.1.const_smul a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2, mul_zero]
  let F : C(Γ, ℂ) := ⟨fun k => star (f k), hf.star⟩
  let f' : C(Γ, ℂ) := ⟨f, hf⟩
  have hclose := dense hK hH F
  have hbound : ∀ ε > 0, ‖∫ k, F k * f k ∂μ‖ ≤ ε * (‖f'‖ * μ.real Set.univ) := by
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hclose ε hε
    have hb' := hspan b hb
    have heq : ∫ k, F k * f k ∂μ = ∫ k, (F k - b k) * f k ∂μ := by
      rw [← sub_zero (∫ k, F k * f k ∂μ), ← hb'.2, ← integral_sub
        (integrable_of_cont μ (f := fun k => F k * f k) (F.continuous.mul hf))
        (integrable_of_cont μ (f := fun k => b k * f k) (b.continuous.mul hf))]
      congr 1
      funext k
      ring
    rw [heq, ← mul_assoc]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul]
    have h1 : ‖F k - b k‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (F - b) k
      rw [dist_eq_norm] at hdist
      simp only [ContinuousMap.sub_apply] at this
      linarith
    have h2 : ‖f k‖ ≤ ‖f'‖ := ContinuousMap.norm_coe_le_norm f' k
    exact mul_le_mul h1 h2 (norm_nonneg _) hε.le
  have hzero : ∫ k, F k * f k ∂μ = 0 := by
    by_contra hne
    have hpos : 0 < ‖∫ k, F k * f k ∂μ‖ := norm_pos_iff.2 hne
    set C := ‖f'‖ * μ.real Set.univ
    have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) measureReal_nonneg
    set x := ‖∫ k, F k * f k ∂μ‖
    have := hbound (x / (2 * (C + 1))) (by positivity)
    have h3 : x / (2 * (C + 1)) * C ≤ x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hre : ∀ k, F k * f k = ((‖f k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [F, ContinuousMap.coe_mk]
    rw [Complex.ofReal_pow]
    exact RCLike.conj_mul (f k)
  simp_rw [hre, integral_complex_ofReal, Complex.ofReal_eq_zero] at hzero
  have hint : Integrable (fun k => ‖f k‖ ^ 2) μ := by
    have := (integrable_of_cont μ (f := fun k => ((‖f k‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)).re
    exact this
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖f k‖) hint).1 hzero
  have hfun := (Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae
  have h0 : ‖f x‖ ^ 2 = 0 := congrFun hfun x
  exact hx (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))

end SWS

end PositivityTheory.Rg.Cz

end
