import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

def intMap (hU : IsUnrExt K K' d φ) : K.O →+* K'.O where
  toFun a := Classical.choose (exists_int_image hU a)
  map_one' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 1)]; simp)
  map_mul' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a * b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_mul, h2, h3])
  map_zero' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 0)]; simp)
  map_add' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a + b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_add, h2, h3])

theorem intMap_spec (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) :=
  Classical.choose_spec (exists_int_image hU a)

theorem intMap_injective (hU : IsUnrExt K K' d φ) : Function.Injective (intMap hU) := by
  intro a b h
  apply IsFractionRing.injective K.O K.E
  apply φ.injective
  rw [← intMap_spec hU, ← intMap_spec hU, h]

theorem val_mul_ne (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]; ring

theorem val_irreducible (K : UQ) {ϖ : K.O} (h : Irreducible ϖ) : val K.O (algebraMap K.O K.E ϖ) = 1 := by
  unfold val
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h), WithZero.log_exp]; rfl

theorem val_pow_ne (K : UQ) {x : K.E} (hx : x ≠ 0) (n : ℕ) : val K.O (x ^ n) = n * val K.O x := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_ne K (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem val_isUnit (K : UQ) {u : K.O} (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : (algebraMap K.O K.E (w : K.O)) ≠ 0 := by simp
  have h2 : (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) ≠ 0 := by simp
  have h := val_mul_ne K h1 h2
  rw [← map_mul, Units.mul_inv, map_one] at h
  have h3 := val_algebraMap_nonneg K (w : K.O)
  have h4 := val_algebraMap_nonneg K ((w⁻¹ : K.Oˣ) : K.O)
  have h5 : val K.O (1 : K.E) = 0 := by simp [val]
  omega

theorem irreducible_of_val_one (K : UQ) {x : K.O} (hx : val K.O (algebraMap K.O K.E x) = 1) :
    Irreducible x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [val] at hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap K.O K.E (u : K.O) ≠ 0 := by simp
  rw [map_mul, map_pow, val_mul_ne K hu0 (pow_ne_zero _ hϖ0), val_pow_ne K hϖ0,
    val_isUnit K u.isUnit, val_irreducible K hϖ] at hx
  have hn : n = 1 := by omega
  subst hn
  rw [pow_one]
  exact (irreducible_units_mul u).2 hϖ

theorem map_maximalIdeal (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have h1 := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h2 : Irreducible (intMap hU ϖ) :=
    irreducible_of_val_one K' (by rw [intMap_spec, hU.2.2.1, val_irreducible K hϖ])
  rw [h1, Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 h2]

open scoped nonZeroDivisors in

theorem exists_trace_unit_of_span (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.O := (intMap hU).toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K.O K'.O K'.E := IsScalarTower.of_algebraMap_eq fun a => (intMap_spec hU a).symm
  have hmap : ∀ a : K.O, algebraMap K.O K'.O a = intMap hU a := fun _ => rfl

  obtain ⟨u, hu⟩ := hB
  haveI hfin : Module.Finite K.O K'.O := by
    classical
    refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hmap, intMap_spec]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI : FaithfulSMul K.O K'.O :=
    (faithfulSMul_iff_algebraMap_injective K.O K'.O).2 (intMap_injective hU)
  haveI : Module.Free K.O K'.O := Module.free_of_finite_type_torsion_free'

  haveI : IsLocalization (Algebra.algebraMapSubmonoid K'.O K.O⁰) K'.E := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have hφϖ : φ (algebraMap K.O K.E ϖ) ≠ 0 := by simpa using hϖ0
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := hy
      refine IsUnit.mk0 _ ?_
      change algebraMap K'.O K'.E (intMap hU r) ≠ 0
      rw [intMap_spec]
      simpa using nonZeroDivisors.ne_zero hr
    · intro z
      by_cases hz : z = 0
      · exact ⟨⟨0, 1⟩, by simp [hz]⟩
      obtain ⟨s, hs⟩ := mem_range_of_val_nonneg K'
        (z * φ (algebraMap K.O K.E ϖ) ^ (-(val K'.O z)).toNat) (by
          rw [val_mul_ne K' hz (pow_ne_zero _ hφϖ), val_pow_ne K' hφϖ, hU.2.2.1, val_irreducible K hϖ]
          omega)
      refine ⟨⟨s, ⟨algebraMap K.O K'.O (ϖ ^ (-(val K'.O z)).toNat),
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩⟩⟩, ?_⟩
      change z * algebraMap K'.O K'.E (intMap hU (ϖ ^ (-(val K'.O z)).toNat)) = algebraMap K'.O K'.E s
      rw [hs, intMap_spec, map_pow, map_pow]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective K'.O K'.E h]⟩

  have hpS : Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O) =
      IsLocalRing.maximalIdeal K'.O := map_maximalIdeal hU
  haveI hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hpS]; infer_instance
  letI : Field (K.O ⧸ IsLocalRing.maximalIdeal K.O) := Ideal.Quotient.field _
  letI : Field (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Ideal.Quotient.field _
  haveI : Finite (K'.O ⧸ IsLocalRing.maximalIdeal K'.O) := K'.fin
  haveI : Finite (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq hpS).symm.toEquiv
  haveI : Finite (K.O ⧸ IsLocalRing.maximalIdeal K.O) := K.fin
  haveI : FiniteDimensional (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  haveI : Algebra.IsSeparable (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (K.O ⧸ IsLocalRing.maximalIdeal K.O)
    (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have htr := Algebra.trace_quotient_mk (R := K.O) (S := K'.O) y
  rw [hz] at htr
  refine ⟨y, Algebra.trace K.O K'.O y, ?_, ?_⟩
  · by_contra h
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal K.O) (Algebra.trace K.O K'.O y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h0] at htr
    exact one_ne_zero htr
  · exact Algebra.trace_localization K.O K.O⁰ (Rₘ := K.E) (Sₘ := K'.E) y

theorem exists_trace_unit (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  exists_trace_unit_of_span K K' d φ hU (exists_int_basis_of_unr K K' d φ hU)

end GlobalTheory.UnitLemma.Unr
