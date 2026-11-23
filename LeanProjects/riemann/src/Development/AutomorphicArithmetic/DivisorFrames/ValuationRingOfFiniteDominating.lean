import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

private theorem dedekind_local_divisibility (S : Type) [CommRing S] [IsDedekindDomain S] (P : Ideal S) [P.IsPrime]
    (a b : S) (hb : b ≠ 0) : ∃ u v : S, v ∉ P ∧ (a * u = b * v ∨ b * u = a * v) := by
  by_cases hP : P = ⊥
  · refine ⟨a, b, ?_, Or.inr (mul_comm _ _)⟩
    rw [hP]; simpa using hb
  · haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP
      (Localization.AtPrime P)
    have hinj : Function.Injective (algebraMap S (Localization.AtPrime P)) :=
      IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap S (Localization.AtPrime P) a)
      (algebraMap S (Localization.AtPrime P) b)
    obtain ⟨⟨u, v⟩, huv⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨u, v, v.2, ?_⟩
    simp only at huv
    rcases hc with h | h
    · left
      apply hinj
      rw [map_mul, map_mul, ← huv, ← h, mul_assoc]
    · right
      apply hinj
      rw [map_mul, map_mul, ← huv, ← h, mul_assoc]

theorem UpperTheory.valuationRing_of_finite_dominating :
    ∀ (R K A L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [Field L] [Algebra A L] [IsFractionRing A L] (φ : K →+* L), φ.Finite → ∀ ψ : R →+* A, (∀ r, algebraMap A L (ψ r) = φ (algebraMap R K r)) → ValuationRing A := by
  intro R K A L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ ψ hψ
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hφ
  letI : Algebra R L := (φ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra R A := ψ.toAlgebra
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun r => (hψ r).symm)
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hex : ∀ s : integralClosure R L, ∃ a : A, algebraMap A L a = (s : L) := fun s =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.tower_top (A := A) s.2)
  choose f hf using hex
  let χ : integralClosure R L →+* A :=
    { toFun := f
      map_one' := hinj (by simp [hf])
      map_mul' := fun x y => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun x y => hinj (by simp [hf]) }
  have hχ : ∀ s, algebraMap A L (χ s) = (s : L) := hf
  rw [ValuationRing.iff_isInteger_or_isInteger A L]
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure R L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨u, v, hv, h⟩ := dedekind_local_divisibility _ ((maximalIdeal A).comap χ) a b hb0
  have hvu : IsUnit (χ v) := by
    rw [Ideal.mem_comap] at hv
    exact notMem_maximalIdeal.mp hv
  obtain ⟨w, hw⟩ := hvu.exists_right_inv
  have hw' : (v : L) * algebraMap A L w = 1 := by
    rw [← hχ, ← map_mul, hw, map_one]
  have hbL : (b : L) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
  have hvL : (v : L) ≠ 0 := left_ne_zero_of_mul_eq_one hw'
  change IsLocalization.IsInteger A ((a : L) / (b : L)) ∨
    IsLocalization.IsInteger A ((a : L) / (b : L))⁻¹
  rcases h with h | h
  · right
    have h' : (a : L) * u = b * v := congrArg Subtype.val h
    have haL : (a : L) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h'
      exact mul_ne_zero hbL hvL h'.symm
    refine ⟨χ u * w, ?_⟩
    rw [map_mul, hχ, inv_div, eq_div_iff haL]
    linear_combination algebraMap A L w * h' + (b : L) * hw'
  · left
    have h' : (b : L) * u = a * v := congrArg Subtype.val h
    refine ⟨χ u * w, ?_⟩
    rw [map_mul, hχ, eq_div_iff hbL]
    linear_combination algebraMap A L w * h' + (a : L) * hw'
