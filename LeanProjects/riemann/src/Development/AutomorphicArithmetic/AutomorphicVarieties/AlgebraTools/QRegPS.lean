import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem order_of_mem_pow {O σ : Type} [CommRing O] (n : ℕ) :
    ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ n, (n : ℕ∞) ≤ g.order := by
  have h1 : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      ((1 : ℕ) : ℕ∞) ≤ g.order := by
    intro g hg
    have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ≤
        RingHom.ker (constantCoeff : MvPowerSeries σ O →+* O) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    refine nat_le_order fun d hd => ?_
    have hd0 : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst hd0
    simpa using hle hg
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · refine le_trans ?_ le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih x hx) (h1 y hy)
    · exact le_trans (le_min hx hy) min_order_le_add

private theorem coeff_mem_of_mem_map {O σ : Type} [CommRing O] (I : Ideal O) (g : MvPowerSeries σ O)
    (hg : g ∈ I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)) (d : σ →₀ ℕ) : coeff d g ∈ I := by
  have hle : I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) ≤
      RingHom.ker (MvPowerSeries.map (σ := σ) (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have h := congrArg (coeff d) (RingHom.mem_ker.1 (hle hg))
  rw [coeff_map, map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

private theorem monoVal_X_eq {O σ : Type} [CommRing O] (α : σ →₀ ℕ) :
    GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ O) α = monomial α 1 := by
  simp only [GlobalTheory.monoVal, Finsupp.prod, X_pow_eq, prod_monomial, Finset.prod_const_one]
  congr 2
  exact Finsupp.sum_single α

private theorem eq_of_le_of_degree_eq {σ : Type} {α β : σ →₀ ℕ} (h : β ≤ α)
    (hd : β.degree = α.degree) : β = α := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add] at hd
  have : γ = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.qRegAt_mvPowerSeries :
    ∀ (Λ σ : Type) [CommRing Λ] [Finite σ] (I : Ideal Λ) (a : ℕ),
      QRegAt (MvPowerSeries σ Λ) (MvPowerSeries.X : σ → MvPowerSeries σ Λ) (I.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) a := by
  intro Λ σ _ _ I a c hc α
  classical
  haveI := Fintype.ofFinite σ
  rw [smul_eq_mul, Ideal.mul_top] at hc ⊢
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  have h0 : MvPowerSeries.coeff α.1 u = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ u hu))
    rw [α.2]
    exact_mod_cast Nat.lt_succ_self a
  have h1 : MvPowerSeries.coeff α.1 (u + v) = MvPowerSeries.constantCoeff (c α) := by
    rw [huv, map_sum, Finset.sum_eq_single α]
    · rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul]
      simp
    · intro β _ hβ
      rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul, if_neg]
      intro hle
      exact hβ (Subtype.ext (eq_of_le_of_degree_eq hle (β.2.trans α.2.symm)))
    · simp
  have h2 : MvPowerSeries.constantCoeff (c α) ∈ I := by
    rw [← h1, map_add, h0, zero_add]
    exact coeff_mem_of_mem_map I v hv _
  have h3 : c α = (c α - MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))) +
      MvPowerSeries.C (MvPowerSeries.constantCoeff (c α)) := by ring
  rw [h3]
  exact Submodule.add_mem_sup (mem_span_X _ (by simp)) (Ideal.mem_map_of_mem _ h2)
