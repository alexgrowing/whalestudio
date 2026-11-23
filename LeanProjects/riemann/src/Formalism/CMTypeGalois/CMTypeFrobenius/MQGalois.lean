import Mathlib
import Formalism.CMTypeGalois.StatementField

open Polynomial

noncomputable section

namespace Formalism.Q3

section MQ

variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}

lemma mq_alpha_ne_zero (h : IsMQ a α) (ha : ∀ i, a i ≠ 0) (i : Fin k) : α i ≠ 0 := by
  intro h0
  have h2 := h.1 i
  rw [h0, zero_pow two_ne_zero] at h2
  exact ha i (by exact_mod_cast h2.symm)

lemma mq_sigma (h : IsMQ a α) (σ : Gal(E/ℚ)) (i : Fin k) :
    σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := by
  have hsq : (σ (α i)) ^ 2 = (α i) ^ 2 := by
    rw [← map_pow, h.1 i, map_intCast]
  unfold galSign
  split_ifs with hs
  · simp [hs]
  · have : (σ (α i) - α i) * (σ (α i) + α i) = 0 := by ring_nf; rw [hsq]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hs
    · simp [eq_neg_of_add_eq_zero_left h1]

lemma mq_galSign_mul (h : IsMQ a α) (ha : ∀ i, a i ≠ 0) (σ τ : Gal(E/ℚ)) :
    galSign α (σ * τ) = galSign α σ * galSign α τ := by
  funext i
  have hne := mq_alpha_ne_zero h ha i
  have hστ := mq_sigma h (σ * τ) i
  rw [AlgEquiv.mul_apply, mq_sigma h τ i, map_mul, map_intCast, mq_sigma h σ i] at hστ
  have hcoef : (((galSign α (σ * τ) i : ℤˣ) : ℤ) : E) = (((galSign α σ i * galSign α τ i : ℤˣ) : ℤ) : E) := by
    have := hστ.symm
    rw [show ((((galSign α τ i : ℤˣ) : ℤ) : E) * ((((galSign α σ i : ℤˣ) : ℤ) : E) * α i)) =
      (((galSign α σ i * galSign α τ i : ℤˣ) : ℤ) : E) * α i by push_cast; ring] at this
    exact mul_right_cancel₀ hne this
  have := Int.cast_injective (α := E) hcoef
  exact Units.ext this

lemma mq_algAdjoin (h : IsMQ a α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by
  have halg : ∀ x ∈ Set.range α, IsAlgebraic ℚ x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, h.2]
  rfl

lemma mq_injective (h : IsMQ a α) : Function.Injective (galSign α) := by
  intro σ τ hst
  have hsub : ∀ x ∈ Set.range α, (σ : E →ₐ[ℚ] E) x = (τ : E →ₐ[ℚ] E) x := by
    rintro _ ⟨i, rfl⟩
    simp only [AlgEquiv.coe_algHom]
    rw [mq_sigma h σ i, mq_sigma h τ i, hst]
  have := AlgHom.ext_of_adjoin_eq_top (mq_algAdjoin h) hsub
  ext x
  exact DFunLike.congr_fun this x

lemma mq_isGalois (h : IsMQ a α) : IsGalois ℚ E := by
  classical
  set p : ℚ[X] := ∏ i, (X ^ 2 - C ((a i : ℚ))) with hp
  have hmon : p.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C _ two_ne_zero)
  have hroot : ∀ i, α i ∈ p.rootSet E := by
    intro i
    rw [mem_rootSet]
    refine ⟨hmon.ne_zero, ?_⟩
    rw [hp, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [h.1 i]
  have hsplit : (p.map (algebraMap ℚ E)).Splits := by
    rw [hp, Polynomial.map_prod]
    apply Splits.prod
    intro i _
    have hfac : (X ^ 2 - C ((a i : ℚ))).map (algebraMap ℚ E) = (X - C (α i)) * (X - C (-α i)) := by
      have hc : (C ((a i : ℚ))).map (algebraMap ℚ E) = C (α i) ^ 2 := by
        rw [Polynomial.map_C, map_intCast, ← h.1 i, C_pow]
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hc, C_neg]
      ring
    rw [hfac]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
  haveI : p.IsSplittingField ℚ E := by
    refine Polynomial.IsSplittingField.mk hsplit ?_
    rw [eq_top_iff, ← mq_algAdjoin h]
    exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact hroot i)
  haveI : Normal ℚ E := Normal.of_isSplittingField p
  exact IsGalois.mk

end MQ

section Exists

variable {k : ℕ} (a : Fin k → ℤ)

lemma exists_square_roots_closure : ∃ β : Fin k → AlgebraicClosure ℚ, ∀ i, β i ^ 2 = (a i : AlgebraicClosure ℚ) := by
  choose β hβ using fun i => IsAlgClosed.exists_pow_nat_eq ((a i : AlgebraicClosure ℚ)) two_pos
  exact ⟨β, hβ⟩

end Exists

private lemma adjoin_range_subtype_eq_whole_field {L : Type} [Field L] [Algebra ℚ L] (K : IntermediateField ℚ L)
    {k : ℕ} (β : Fin k → L) (hK : K = IntermediateField.adjoin ℚ (Set.range β)) (α' : Fin k → K)
    (hα : ∀ i, (α' i : L) = β i) :
    @IntermediateField.adjoin ℚ _ K _ K.algebra' (Set.range α') = ⊤ := by
  letI : Algebra ℚ K := K.algebra'
  have himg : K.val '' Set.range α' = Set.range β := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hα i
  have hmap := IntermediateField.adjoin_map ℚ (Set.range α') K.val
  rw [himg, ← hK] at hmap
  rw [eq_top_iff]
  intro x _
  have hx : (x : L) ∈ (IntermediateField.adjoin ℚ (Set.range α')).map K.val := by
    rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 hx
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

lemma adjoin_subtype_top {L : Type} [Field L] [Algebra ℚ L] (K : IntermediateField ℚ L)
    {k : ℕ} (β : Fin k → L) (hK : K = IntermediateField.adjoin ℚ (Set.range β)) (α' : Fin k → K)
    (hα : ∀ i, (α' i : L) = β i) [inst : Algebra ℚ K] :
    IntermediateField.adjoin ℚ (Set.range α') = ⊤ := by
  obtain rfl : inst = K.algebra' := Subsingleton.elim _ _
  exact adjoin_range_subtype_eq_whole_field K β hK α' hα

theorem mqGalois : MQGalois := by
  intro k E _ _ a α h ha
  exact ⟨mq_isGalois h, mq_sigma h, mq_galSign_mul h ha, mq_injective h⟩

theorem mqExists : MQExists := by
  intro k a
  obtain ⟨β, hβ⟩ := exists_square_roots_closure a
  set K := IntermediateField.adjoin ℚ (Set.range β) with hK
  have hint : ∀ x ∈ Set.range β, IsIntegral ℚ x := by
    rintro _ ⟨i, rfl⟩
    refine ⟨X ^ 2 - C ((a i : ℚ)), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hβ i, map_intCast, sub_self]
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hint
  haveI : NumberField K := ⟨⟩
  let α' : Fin k → K := fun i => ⟨β i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  refine ⟨K, inferInstance, inferInstance, α', ?_, ?_⟩
  · intro i
    apply Subtype.ext
    simp [α', hβ i]
  · exact adjoin_subtype_top K β hK α' (fun i => rfl)

end Formalism.Q3
