import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable
open IsLocalRing UpperTheory.V.Alg

open MvPowerSeries in
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

section Abstract

variable {O R A : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing A] [Algebra O A]

private def Appr (φ : R →ₐ[O] A) (J : Ideal A) (f : A) : Prop :=
  ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ J

private theorem appr_zero (φ : R →ₐ[O] A) (J : Ideal A) : Appr φ J 0 :=
  ⟨0, 1, one_ne_zero, by simp⟩

private theorem appr_add {φ : R →ₐ[O] A} {J : Ideal A} {f g : A} (hf : Appr φ J f) (hg : Appr φ J g) :
    Appr φ J (f + g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨d • a + e • b, e * d, mul_ne_zero he hd, ?_⟩
  have : (e * d) • (f + g) - φ (d • a + e • b) =
      algebraMap O A d * (e • f - φ a) + algebraMap O A e * (d • g - φ b) := by
    rw [map_add, map_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ h')

private theorem appr_mul {φ : R →ₐ[O] A} {m : Ideal A} {i j : ℕ} {f g : A} (hfm : f ∈ m ^ i) (hgm : g ∈ m ^ j)
    (hf : Appr φ (m ^ (i + 1)) f) (hg : Appr φ (m ^ (j + 1)) g) : Appr φ (m ^ (i + j + 1)) (f * g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨a * b, e * d, mul_ne_zero he hd, ?_⟩
  have hb : φ b ∈ m ^ j := by
    have h1 : φ b = algebraMap O A d * g - (d • g - φ b) := by
      rw [Algebra.smul_def]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgm) (Ideal.pow_le_pow_right (Nat.le_succ j) h')
  have : (e * d) • (f * g) - φ (a * b) =
      algebraMap O A e * (f * (d • g - φ b)) + (e • f - φ a) * φ b := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul hfm h'
  · rw [add_right_comm, pow_add]
    exact Ideal.mul_mem_mul h hb

private theorem appr_step {φ : R →ₐ[O] A} {m : Ideal A} (h0 : ∀ f, Appr φ (m ^ (0 + 1)) f)
    (h1 : ∀ f ∈ m, Appr φ (m ^ (1 + 1)) f) (N : ℕ) : ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f := by
  induction N with
  | zero => exact fun f _ => h0 f
  | succ N ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => appr_add ha hb)
    exact appr_mul (j := 1) ha (by rwa [pow_one]) (ih a ha) (h1 b hb)

private theorem appr_all {φ : R →ₐ[O] A} {m : Ideal A} (h : ∀ N, ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f)
    (N : ℕ) (f : A) : Appr φ (m ^ N) f := by
  induction N with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | succ N ih =>
    obtain ⟨a, e, he, ha⟩ := ih
    obtain ⟨b, d, hd, hb⟩ := h N _ ha
    refine ⟨d • a + b, d * e, mul_ne_zero hd he, ?_⟩
    have : (d * e) • f - φ (d • a + b) = d • (e • f - φ a) - φ b := by
      rw [map_add, map_smul]
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [this]
    exact hb

end Abstract

theorem UpperTheory.power_series_approximation_mod_maximal :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O), c ≠ 0 → (∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (f : MvPowerSeries (Fin n) E), ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
  intro O E _ _ _ _ _ R _ _ n φ t c hc ht N f
  have hmem : ∀ g : MvPowerSeries (Fin n) E,
      g ∈ maximalIdeal (MvPowerSeries (Fin n) E) ↔ MvPowerSeries.constantCoeff g = 0 := fun g => by
    simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
      not_not]
  have h0 : ∀ g, Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (0 + 1)) g := by
    intro g
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) (MvPowerSeries.constantCoeff g)
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hy1 : algebraMap O E y ≠ 0 := fun h => hy0 (IsFractionRing.injective O E (by rw [h, map_zero]))
    refine ⟨algebraMap O R x, y, hy0, ?_⟩
    rw [zero_add, pow_one, hmem, AlgHom.commutes, Algebra.smul_def, map_sub, map_mul, ← hxy,
      MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C,
      MvPowerSeries.constantCoeff_C]
    rw [mul_div_cancel₀ _ hy1, sub_self]
  have h1 : ∀ g ∈ maximalIdeal (MvPowerSeries (Fin n) E),
      Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (1 + 1)) g := by
    intro g hg
    have hs := mem_span_X g ((hmem g).1 hg)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine Finset.sum_induction _ _ (fun a b ha hb => appr_add ha hb) (appr_zero _ _) fun i _ => ?_
    refine appr_mul (i := 0) (j := 1) (by simp) (by rw [pow_one, hmem]; simp) (h0 _) ⟨t i, c, hc, ?_⟩
    have h2 := neg_mem (ht i)
    rwa [neg_sub] at h2
  exact appr_all (appr_step h0 h1) N f
