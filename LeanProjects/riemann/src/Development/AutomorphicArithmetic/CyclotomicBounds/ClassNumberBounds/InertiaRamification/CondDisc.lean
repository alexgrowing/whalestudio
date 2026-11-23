import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.RootNorm
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Filtration
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem isPrimitiveRoot_pow_val {R : Type*} [CommRing R] {z : R}
    (hz : IsPrimitiveRoot z N) (a : ZMod N) : IsPrimitiveRoot (z ^ a.val) (addOrderOf a) := by
  have h1 : addOrderOf a = orderOf (z ^ a.val) := by
    have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨N, NeZero.pos N, hz.pow_eq_one⟩
    rw [hfin.orderOf_pow, ← hz.eq_orderOf, ← ZMod.addOrderOf_coe _ (NeZero.ne N),
      ZMod.natCast_zmod_val]
  rw [h1]
  exact IsPrimitiveRoot.orderOf _

private theorem span_sub_smul {z : 𝓞 K} (hz : IsPrimitiveRoot z N) (σ : Gal(K/ℚ)) :
    Ideal.span {z - σ • z} =
      Ideal.span {1 - z ^ ((galEquivZMod N K σ : ZMod N) - 1).val} := by
  rw [galEquivZMod_smul_of_pow_eq N K σ hz.pow_eq_one]
  have h : z ^ (galEquivZMod N K σ).val.val =
      z ^ (1 + ((galEquivZMod N K σ : ZMod N) - 1).val) := by
    refine pow_eq_pow_of_modEq ?_ hz.pow_eq_one
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [h, pow_add, pow_one, ← mul_one_sub]
  exact Ideal.span_singleton_mul_left_unit (hz.isUnit (NeZero.ne N)) _

private theorem padicValNat_prod {ι : Type*} (l : ℕ) [Fact l.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat l (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat l (f i) := by
  have hl : l.Prime := Fact.out
  simp only [← Nat.factorization_def _ hl]
  rw [Nat.factorization_prod hf, Finsupp.finsetSum_apply]

private theorem vdField_eq_avg (E : IntermediateField ℚ K) (l : ℕ) [Fact l.Prime] :
    vdField E l = avgCondExp l (fieldChars N E) := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have hz := hζ.toInteger_isPrimitiveRoot
  have h := congrArg Ideal.absNorm (map_differentIdeal_eq_span_prod E hζ)
  rw [Ideal.absNorm_algebraMap, absNorm_differentIdeal E,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K, ← Ideal.prod_span_singleton, map_prod] at h
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hne' := h ▸ pow_ne_zero (Module.finrank E K) hne
  have h2 := congrArg (padicValNat l) h
  rw [padicValNat.pow, padicValNat_prod l _ _ (Finset.prod_ne_zero_iff.1 hne')] at h2
  have h3 := congrArg (Nat.cast : ℕ → ℚ) h2
  push_cast at h3
  have h4 : ∀ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      (padicValNat l (Ideal.absNorm (Ideal.span {hζ.toInteger - σ • hζ.toInteger})) : ℚ) =
        Module.finrank ℚ K * rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) := by
    intro σ hσ
    rw [span_sub_smul hz σ]
    refine padicValNat_absNorm_one_sub l ?_ (isPrimitiveRoot_pow_val hz _)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact (Finset.mem_filter.1 hσ).2 (one_mem _)
    have hpos := addOrderOf_pos ((galEquivZMod N K σ : ZMod N) - 1)
    have hne1 : addOrderOf ((galEquivZMod N K σ : ZMod N) - 1) ≠ 1 := by
      rw [Ne, AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero, Units.val_eq_one,
        map_eq_one_iff _ (galEquivZMod N K).injective]
      exact hσ1
    omega
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum] at h3
  have h5 : ∑ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) =
      avgCondExp l (fieldChars N E) := by
    rw [fieldChars, ← sum_rootWeight_eq_avgCondExp]
    refine Finset.sum_equiv (galEquivZMod N K).toEquiv ?_ (fun _ _ => rfl)
    intro σ
    rw [Finset.mem_filter_univ, Finset.mem_filter_univ, fieldUnits]
    exact not_congr (Subgroup.mem_map_iff_mem (f := (galEquivZMod N K).toMonoidHom)
      (galEquivZMod N K).injective).symm
  rw [h5, ← Module.finrank_mul_finrank ℚ E K] at h3
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have p2 : (Module.finrank E K : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [vdField, padicValInt, div_eq_iff p1]
  push_cast at h3
  apply mul_left_cancel₀ p2
  rw [h3]; ring

theorem natAbs_discr_eq_finprod_conductor (E : IntermediateField ℚ K) :
    (discr E).natAbs = ∏ᶠ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor ∧
      Real.log (rootDiscr E) = logRootDiscChar (fieldChars N E) ∧
      (discr E).natAbs.primeFactors = (fieldCond (fieldChars N E)).primeFactors := by
  classical
  have := Fintype.ofFinite (fieldChars N E)
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hc : ∀ ψ : DirichletCharacter ℂ N, ψ.conductor ≠ 0 := fun ψ => conductor_ne_zero ψ
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hcard := (card_fieldChars (N := N) E).1
  have h1 : (discr E).natAbs = ∏ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor := by
    refine Nat.eq_of_factorization_eq hne (Finset.prod_ne_zero_iff.2 fun ψ _ => hc _) fun l => ?_
    by_cases hl : l.Prime
    · have : Fact l.Prime := ⟨hl⟩
      have h := vdField_eq_avg (N := N) E l
      rw [vdField, avgCondExp, hcard, div_left_inj' p1, finsum_eq_sum_of_fintype, padicValInt] at h
      rw [Nat.factorization_prod fun ψ _ => hc _, Finsupp.finsetSum_apply,
        Nat.factorization_def _ hl]
      exact_mod_cast h
    · simp [Nat.factorization_eq_zero_of_not_prime _ hl]
  refine ⟨by rw [finprod_eq_prod_of_fintype, h1], ?_, ?_⟩
  · have habs : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := by
      rw [← Int.natCast_natAbs, Int.cast_natCast]
    rw [rootDiscr_def, logRootDiscChar, hcard, finsum_eq_sum_of_fintype, habs,
      Real.log_rpow (by exact_mod_cast Nat.pos_of_ne_zero hne), h1, Nat.cast_prod,
      Real.log_prod (fun ψ _ => by exact_mod_cast hc _), div_eq_inv_mul]
  · have hf : fieldCond (fieldChars N E) ≠ 0 := by
      rw [fieldCond, Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨ψ, -, h⟩
      exact hc ψ h
    ext l
    rw [Nat.mem_primeFactors_of_ne_zero hne, Nat.mem_primeFactors_of_ne_zero hf]
    refine and_congr_right fun hl => ?_
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨a, b, -⟩ := ramIdx_eq_one_iff l (fieldChars N E)
    rw [h1, hl.prime.dvd_finsetProd_iff, ← not_iff_not, ← b, a]
    simp

end KStar.Ram
