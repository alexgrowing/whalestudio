import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

namespace GlobalTheory.FiniteQuotOmega

open MvPowerSeries IsLocalRing
open scoped TensorProduct

section General

variable {T Q σ : Type*} [CommRing T] [CommRing Q] [Algebra T Q] [Fintype σ]

theorem derivation_apply_eq_sum [IsNoetherianRing Q] {M : Type*} [AddCommGroup M] [Module T M]
    [Module Q M] [Module.Finite Q M] (φ : MvPowerSeries σ T →ₐ[T] Q)
    (hφ : Function.Surjective φ) (D : Derivation T Q M) (g : MvPowerSeries σ T) :
    D (φ g) = ∑ j, φ (pderiv T j g) • D (φ (X j)) := by
  classical
  set J : Ideal Q := Ideal.jacobson ⊥ with hJ
  have hX : ∀ i, φ (X i) ∈ J := by
    intro i
    rw [hJ, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨h, rfl⟩ := hφ y
    have : IsUnit (X i * h + 1 : MvPowerSeries σ T) := by
      rw [isUnit_iff_constantCoeff]; simp
    simpa using this.map φ
  have key : ∀ (n : ℕ) (g : MvPowerSeries σ T),
      D (φ g) - ∑ j, φ (pderiv T j g) • D (φ (X j)) ∈ (J ^ n • ⊤ : Submodule Q M) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
        fun d hd => by
          have : d = 0 := by
            rw [← Finsupp.degree_eq_zero_iff]; omega
          subst this
          simp
      have hg : g = C (constantCoeff g) + ∑ i, X i * k i := by rw [← hk]; ring
      have hC : ∀ c : T, D (φ (C c)) = 0 := fun c => by
        have : φ (C c) = algebraMap T Q c := φ.commutes c
        rw [this, Derivation.map_algebraMap]
      have h1 : ∀ i, ∑ j, φ (pderiv T j (X i * k i)) • D (φ (X j)) =
          φ (X i) • ∑ j, φ (pderiv T j (k i)) • D (φ (X j)) + φ (k i) • D (φ (X i)) := by
        intro i
        simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_smul,
          Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [pderiv_X_of_ne hj.symm]
        · simp
      have e : D (φ g) - ∑ j, φ (pderiv T j g) • D (φ (X j)) =
          ∑ i, φ (X i) • (D (φ (k i)) - ∑ j, φ (pderiv T j (k i)) • D (φ (X j))) := by
        generalize constantCoeff g = c at hg
        subst hg
        simp only [map_add, hC, zero_add, pderiv_C, map_sum, Finset.sum_smul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1, map_mul, Derivation.leibniz, smul_sub]
        abel
      rw [e, pow_succ', mul_smul]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hX i) (ih _)
  rw [← sub_eq_zero, ← Submodule.mem_bot Q,
    ← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) J le_rfl, Submodule.mem_iInf]
  exact fun n => key n g

theorem det_smul_kaehler_eq_zero [DecidableEq σ] [IsNoetherianRing T] [Module.Finite T Q]
    (φ : MvPowerSeries σ T →ₐ[T] Q) (hφ : Function.Surjective φ) (f : σ → MvPowerSeries σ T)
    (hf : ∀ i, φ (f i) = 0) (ω : KaehlerDifferential T Q) :
    φ (Matrix.det (Matrix.of fun i j => pderiv T j (f i))) • ω = 0 := by
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite T Q
  set D := KaehlerDifferential.D T Q with hD
  set A : Matrix σ σ Q := Matrix.of fun i j => φ (pderiv T j (f i)) with hA
  have hdet : φ (Matrix.det (Matrix.of fun i j => pderiv T j (f i))) = A.det := by
    rw [AlgHom.map_det]; rfl
  have hrel : ∀ i, ∑ j, A i j • D (φ (X j)) = 0 := fun i => by
    have := derivation_apply_eq_sum φ hφ D (f i)
    rw [hf, map_zero] at this
    exact this.symm
  have hx : ∀ l, A.det • D (φ (X l)) = 0 := fun l => by
    have h : ∑ j, (A.adjugate * A) l j • D (φ (X j)) = 0 := by
      simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hrel, smul_zero, Finset.sum_const_zero]
    rw [Matrix.adjugate_mul] at h
    simpa [Matrix.one_apply] using h
  rw [hdet]
  have hω : ω ∈ Submodule.span Q (Set.range D) := by
    rw [hD, KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x h =>
    obtain ⟨y, rfl⟩ := h
    obtain ⟨g, rfl⟩ := hφ y
    rw [derivation_apply_eq_sum φ hφ D g, Finset.smul_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, hx, smul_zero]
  | zero => simp
  | add x y _ _ h1 h2 => rw [smul_add, h1, h2, add_zero]
  | smul a x _ h => rw [smul_comm, h, smul_zero]

end General

theorem jacobian_smul_kaehler_eq_zero :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ : Type) [Fintype σ] [DecidableEq σ] (f : σ → MvPowerSeries σ T), Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ ω : KaehlerDifferential T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)), (Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => pderiv T j (f i)))) • ω = 0 := by
  intro T _ _ _ σ _ _ f hfin ω
  exact det_smul_kaehler_eq_zero (Ideal.Quotient.mkₐ T (Ideal.span (Set.range f)))
    Ideal.Quotient.mk_surjective f
    (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)) ω

end GlobalTheory.FiniteQuotOmega
