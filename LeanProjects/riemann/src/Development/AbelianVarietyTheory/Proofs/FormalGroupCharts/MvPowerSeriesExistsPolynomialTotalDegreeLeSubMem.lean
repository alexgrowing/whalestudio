import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem

open IsLocalRing TensorProduct

namespace GlobalTheory.CompleteBaseChange

open MvPowerSeries

theorem monomial_one_mem_span_X_pow {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    (monomial α (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ α.degree := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : (monomial (a + b) (1 : R) : MvPowerSeries σ R) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_add, pow_add]
    exact Ideal.mul_mem_mul ha hb
  | single s n =>
    rw [← X_pow_eq, Finsupp.degree_single]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self s)) n

theorem exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  intro O _ J hJ hO σ τ _ _ f N hM g
  have := Fintype.ofFinite τ
  have hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O) := fun α hα =>
    hM (hα ▸ monomial_one_mem_span_X_pow α)
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), ?_,
    Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  · refine Finset.sup_le fun d hd => ?_
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hd (coeff_truncTotal_eq_zero _ ?_)
    exact (not_le.1 hlt).le
  · rw [← hx]
    exact (add_sub_cancel_left _ _).symm

end GlobalTheory.CompleteBaseChange
