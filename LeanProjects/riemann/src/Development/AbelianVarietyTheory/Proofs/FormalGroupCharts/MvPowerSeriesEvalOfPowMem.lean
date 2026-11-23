import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing TensorProduct

namespace GlobalTheory

namespace NilpotentEval

variable {A : Type*} [CommRing A]

theorem pow_mul_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (n : ℕ) : J ^ (N * n) ≤ K ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono h n

theorem isHausdorff_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) [IsHausdorff K A] :
    IsHausdorff J A := by
  refine ⟨fun x hx => IsHausdorff.haus' (I := K) x fun n => ?_⟩
  have := hx (N * n)
  rw [SModEq.zero] at this ⊢
  simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
  exact pow_mul_le h n this

theorem isPrecomplete_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (hKJ : K ≤ J)
    [IsPrecomplete K A] : IsPrecomplete J A := by
  have h' : J ^ (N + 1) ≤ K := (Ideal.pow_le_pow_right N.le_succ).trans h
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := K) (fun n => f ((N + 1) * n)) fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact pow_mul_le h' m (hf (Nat.mul_le_mul_left _ hmn))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
  have h2 := Ideal.pow_right_mono hKJ n (hL n)
  simpa using add_mem h1 h2

theorem exists_pow_sup_span_le (K : Ideal A) {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ j, ∃ M : ℕ, a j ^ M ∈ K) : ∃ N : ℕ, (K ⊔ Ideal.span (Set.range a)) ^ N ≤ K := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Ideal.span (Set.range a) ^ N ≤ K :=
    Ideal.exists_pow_le_of_le_radical_of_fg
      (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ha j))
      (Submodule.fg_span (Set.finite_range a))
  refine ⟨N, ?_⟩
  rw [← Ideal.mk_ker (I := K), ← Ideal.map_eq_bot_iff_le_ker] at hN
  conv_rhs => rw [← Ideal.mk_ker (I := K)]
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, ← Ideal.map_pow]
  exact hN

end NilpotentEval

open NilpotentEval in

theorem mvPowerSeries_eval_of_pow_mem : ∀ (A : Type) [CommRing A] (K : Ideal A) (σ : Type) [Finite σ] (a : σ → A), (∀ j, ∃ M : ℕ, a j ^ M ∈ K) → (IsAdicComplete K A → ∀ (R : Type) [CommRing R] [Algebra R A], ∃ ψ : MvPowerSeries σ R →ₐ[R] A, ∀ j, ψ (MvPowerSeries.X j) = a j) ∧ (IsHausdorff K A → ∀ (T : Type) [CommRing T] (ψ ψ' : MvPowerSeries σ T →+* A), (∀ t, ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)) → (∀ j, ψ (MvPowerSeries.X j) = a j) → (∀ j, ψ' (MvPowerSeries.X j) = a j) → ψ = ψ') := by
  intro A _ K σ _ a ha
  obtain ⟨N, hN⟩ := exists_pow_sup_span_le K a ha
  have hmem : ∀ j, a j ∈ K ⊔ Ideal.span (Set.range a) := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨fun hK R _ _ => ?_, fun hK T _ ψ ψ' hC hψ hψ' => ?_⟩
  · haveI : IsAdicComplete (K ⊔ Ideal.span (Set.range a)) A :=
      { toIsHausdorff := isHausdorff_of_pow_le hN
        toIsPrecomplete := isPrecomplete_of_pow_le hN le_sup_left }
    exact ⟨mvEvalAdic R _ a hmem, mvEvalAdic_X _ a hmem⟩
  · haveI := isHausdorff_of_pow_le hN
    letI : Algebra T A := (ψ.comp MvPowerSeries.C).toAlgebra
    let φ : MvPowerSeries σ T →ₐ[T] A := { ψ with commutes' := fun _ => rfl }
    let φ' : MvPowerSeries σ T →ₐ[T] A := { ψ' with commutes' := fun t => (hC t).symm }
    have : φ = φ' := mvPowerSeries_algHom_ext_of_isHausdorff (K ⊔ Ideal.span (Set.range a))
      (fun j => by change ψ _ ∈ _; rw [hψ]; exact hmem j)
      (fun j => (hψ j).trans (hψ' j).symm)
    exact RingHom.ext fun g => DFunLike.congr_fun this g

end GlobalTheory
