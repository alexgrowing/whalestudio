import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory

theorem conjInvariant_sum_zero_eq_sum_log_units (F : Type) [Field F] [NumberField F]
    (c : (F →+* ℂ) → ℝ) (hc : ∀ σ, c ((starRingEnd ℂ).comp σ) = c σ) (hs : ∑ σ, c σ = 0) :
    ∃ (m : ℕ) (u : Fin m → (𝓞 F)ˣ) (r : Fin m → ℝ), ∀ σ,
      c σ = ∑ j, r j * Real.log (‖σ ((u j : 𝓞 F) : F)‖ ^ 2) := by
  classical
  have hfib : ∀ σ : F →+* ℂ, c σ = c (InfinitePlace.mk σ).embedding := by
    intro σ
    have h1 : InfinitePlace.mk σ = InfinitePlace.mk (InfinitePlace.mk σ).embedding := by
      rw [InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · rw [← h]
    · rw [← h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := RingHom.ext fun r => rfl
      rw [this, hc]
  set g : InfinitePlace F → ℝ := fun w => c w.embedding with hg
  have hsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * g w = 0 := by
    rw [← hs, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hf : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), c φ = g w := by
      intro φ hφ
      rw [hfib φ, (Finset.mem_filter.mp hφ).2]
    rw [Finset.sum_congr rfl hf, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  let B := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let v : logSpace F := fun w => (w.1.mult : ℝ) * g w.1 / 2
  let r : Fin (rank F) → ℝ := fun i => B.repr v i
  have hB : ∀ i, (B i : logSpace F) = logEmbedding F (Additive.ofMul (fundSystem F i)) := by
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply, logEmbedding_fundSystem]
  have hv : v = ∑ i, r i • B i := (B.sum_repr v).symm
  set h : InfinitePlace F → ℝ := fun w =>
    g w - ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) with hh
  have hne : ∀ w (hw : w ≠ w₀), h w = 0 := by
    intro w hw
    have hvw := congrFun hv ⟨w, hw⟩
    simp only [v, Finset.sum_apply, Pi.smul_apply, hB, logEmbedding_component, smul_eq_mul] at hvw
    have hvw' : (w.mult : ℝ) * g w / 2 =
        ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F))) := hvw
    have hm : (0 : ℝ) < w.mult := by exact_mod_cast InfinitePlace.mult_pos
    have hS : (w.mult : ℝ) * ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) =
        2 * ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have : (w.mult : ℝ) * h w = 0 := by
      simp only [hh]
      rw [mul_sub, hS, ← hvw']
      ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hm.ne'
    · exact h0
  have htot : ∑ w : InfinitePlace F, (w.mult : ℝ) * h w = 0 := by
    have hi : ∀ i, ∑ w : InfinitePlace F,
        (w.mult : ℝ) * (r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F)))) = 0 := by
      intro i
      have h0 := sum_mult_mul_log (fundSystem F i)
      calc _ = r i * 2 * ∑ w : InfinitePlace F,
            (w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
        _ = 0 := by rw [h0, mul_zero]
    simp only [hh, mul_sub, Finset.sum_sub_distrib, hsum, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_zero fun i _ => hi i, sub_zero]
  have hall : ∀ w, h w = 0 := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      rw [Finset.sum_eq_single w₀ (fun b _ hb => by rw [hne b hb, mul_zero])
        (fun h' => absurd (Finset.mem_univ _) h')] at htot
      have hm : (0 : ℝ) < (w₀ : InfinitePlace F).mult := by exact_mod_cast InfinitePlace.mult_pos
      rcases mul_eq_zero.mp htot with h0 | h0
      · exact absurd h0 hm.ne'
      · exact h0
    · exact hne w hw
  refine ⟨rank F, fundSystem F, r, fun σ => ?_⟩
  have e1 := hall (InfinitePlace.mk σ)
  simp only [hh, sub_eq_zero] at e1
  rw [hfib σ]
  refine e1.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [InfinitePlace.apply, Real.log_pow]
  push_cast
  ring

end GlobalTheory
