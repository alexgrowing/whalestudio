import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfE

namespace LateralTheory.E.E4

open Polynomial

theorem mem_bot_of_mem_adjoin_inv {k L : Type} [Field k] [Field L] [Algebra k L] (t : L) (ht : Transcendental k t)
    (c : L) (h1 : c ∈ Algebra.adjoin k {t}) (h2 : c ∈ Algebra.adjoin k {t⁻¹}) : c ∈ (⊥ : Subalgebra k L) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h1 h2
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, hq⟩ := h2
  have ht0 : t ≠ 0 := by
    rintro rfl; exact ht (isAlgebraic_zero)
  set N := q.natDegree
  have key : aeval t (X ^ N * p) = aeval t (reflect N q) := by
    let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
    have h := eval₂_reflect_mul_pow (algebraMap k L) t⁻¹ N q le_rfl
    rw [invOf_eq_inv, inv_inv] at h
    have hq' : aeval t⁻¹ q = aeval t p := hq
    rw [aeval_def, aeval_def] at hq'
    rw [map_mul, map_pow, aeval_X, aeval_def, aeval_def, ← hq', ← h, mul_comm, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ ht0, one_pow, mul_one]
  have hinj : Function.Injective (aeval t : k[X] →ₐ[k] L) := transcendental_iff_injective.mp ht
  have heq := hinj key
  by_cases hp : p = 0
  · simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (reflect N q).natDegree ≤ N := natDegree_reflect_le.trans (by simp [N])
  have hp0 : p.natDegree = 0 := by rw [heq] at hdeg; omega
  rw [eq_C_of_natDegree_eq_zero hp0]
  simp

def LeafMinpolyCoeff : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (F : IntermediateField k L), F = IntermediateField.adjoin k {s} → ∀ x : L, IsIntegral (Algebra.adjoin k {s}) x →
  ∀ i : ℕ, ((minpoly F x).coeff i : L) ∈ Algebra.adjoin k {s}

theorem isIntegral_adjoin_of {k L : Type} [Field k] [Field L] [Algebra k L] (s : L) (x : L)
    (hx : IsIntegral (Algebra.adjoin k {s}) x) : IsIntegral (IntermediateField.adjoin k {s}) x := by
  obtain ⟨p, hm, hp⟩ := hx
  let ι : Algebra.adjoin k {s} →+* IntermediateField.adjoin k {s} :=
    Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k {s}) |>.toRingHom
  refine ⟨p.map ι, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem LeafIntBoth_of' (hM : LeafMinpolyCoeff) : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L),
    Transcendental k t → ∀ x : L,
    IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x := by
  intro k L _ _ _ t ht x h1 h2
  have ht' : Transcendental k t⁻¹ := fun h => ht (by simpa using h.inv)
  set F := IntermediateField.adjoin k {t}
  have hEq : F = IntermediateField.adjoin k {t⁻¹} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  have hxF : IsIntegral F x := isIntegral_adjoin_of t x h1
  have hc : ∀ i, ((minpoly F x).coeff i : L) ∈ (⊥ : Subalgebra k L) := fun i =>
    mem_bot_of_mem_adjoin_inv t ht _ (hM k L t ht F rfl x h1 i) (hM k L t⁻¹ ht' F hEq x h2 i)
  have hl : minpoly F x ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hc n)
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hxF)
  refine ⟨P, hPm, ?_⟩
  have := minpoly.aeval F x
  rw [← hP, aeval_map_algebraMap] at this
  exact this

theorem LeafIntBoth_of (hM : LeafMinpolyCoeff) : LeafIntBoth := LeafIntBoth_of' hM

theorem LeafOrdAtInfinity_of_cut (hV : LeafOrdInfHom) (hM : LeafMinpolyCoeff) : LeafOrdAtInfinity :=
  LeafOrdAtInfinity_of hV (LeafIntBoth_of hM)

end LateralTheory.E.E4
