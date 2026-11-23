import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem const_of_orthogonal_log_units : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ),
    (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) →
    (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) →
    ∀ sg sg', m sg = m sg' := by
  intro F _ _ m hconj horth
  classical

  have hdesc : ∀ sg sg' : F →+* ℂ, InfinitePlace.mk sg = InfinitePlace.mk sg' → m sg = m sg' := by
    intro sg sg' h
    rcases InfinitePlace.mk_eq_iff.mp h with h | h
    · rw [h]
    · rw [← h, hconj]
  set mw : InfinitePlace F → ℝ := fun w => m w.embedding with hmw
  have hmk : ∀ sg : F →+* ℂ, m sg = mw (InfinitePlace.mk sg) := by
    intro sg
    exact hdesc _ _ (by simp [InfinitePlace.mk_embedding])

  have hplace : ∀ θ : (𝓞 F)ˣ,
      ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * mw w = 0 := by
    intro θ
    rw [← horth θ, ← Finset.sum_fiberwise Finset.univ (fun sg : F →+* ℂ => InfinitePlace.mk sg)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hfib : ∀ sg ∈ Finset.univ.filter (fun sg : F →+* ℂ => InfinitePlace.mk sg = w),
        Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = Real.log (w ((θ : 𝓞 F) : F)) * mw w := by
      intro sg hsg
      have hsg' : InfinitePlace.mk sg = w := (Finset.mem_filter.mp hsg).2
      rw [hmk sg, hsg', ← hsg', InfinitePlace.apply]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul,
      mul_assoc]

  let L : logSpace F →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ w, x w * (mw w.1 - mw w₀)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }
  have hLunit : ∀ θ : (𝓞 F)ˣ, L (logEmbedding F (Additive.ofMul θ)) = 0 := by
    intro θ
    have h1 : ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) = 0 := by
      exact_mod_cast sum_mult_mul_log θ
    have h2 : ∑ w : InfinitePlace F,
        (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * (mw w - mw w₀) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hplace θ, ← Finset.sum_mul, h1]
      simp
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at h2
    simpa [L, logEmbedding_component] using h2
  have hL : L = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
      rw [unitLattice_span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      exact hLunit (Additive.toMul a)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have hconst : ∀ w : InfinitePlace F, mw w = mw w₀ := by
    intro w
    by_cases hw : w = w₀
    · rw [hw]
    · have := LinearMap.congr_fun hL (Pi.single ⟨w, hw⟩ 1)
      have h3 : mw w - mw w₀ = 0 := by
        simpa [L, Pi.single_apply, Finset.sum_ite_eq] using this
      linarith
  intro sg sg'
  rw [hmk sg, hmk sg', hconst (InfinitePlace.mk sg), hconst (InfinitePlace.mk sg')]

end GlobalTheory.CompanionTheory.Ar.Giv
