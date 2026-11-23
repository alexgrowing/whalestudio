import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime

open GlobalTheory.LN

namespace GlobalTheory.ValCrit

open Polynomial in

theorem _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (y : K) (hy : y ≠ 0)
    (h : y⁻¹ ∈ Algebra.adjoin R {y}) : IsIntegral R y⁻¹ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  letI : Invertible y := invertibleOfNonzero hy
  set n := p.natDegree
  have hrefl : (reflect n p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have : (reflect n p).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    exact_mod_cast Nat.lt_succ_of_le this
  refine ⟨X ^ (n + 1) - reflect n p, monic_X_pow_sub hrefl, ?_⟩
  have key := eval₂_reflect_mul_pow (algebraMap R K) y n p le_rfl
  rw [invOf_eq_inv] at key
  have hp' : eval₂ (algebraMap R K) y p = y⁻¹ := hp
  rw [hp'] at key
  have hval : eval₂ (algebraMap R K) y⁻¹ (reflect n p) = y⁻¹ ^ (n + 1) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    rw [← mul_inv_cancel_right₀ hyn (eval₂ (algebraMap R K) y⁻¹ (reflect n p)), key, pow_succ,
      inv_pow, mul_comm]
  rw [eval₂_sub, eval₂_X_pow, hval, sub_self]

private theorem maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin {R K : Type} [CommRing R]
    [IsLocalRing R] [Field K] [Algebra R K] (y : K) (hnot : y⁻¹ ∉ Algebra.adjoin R {y}) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (Algebra.adjoin R {y})) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton R y⟩ : Algebra.adjoin R {y})} ≠ ⊤ := by
  set S := Algebra.adjoin R {y}
  set ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  intro hJ
  set π := Ideal.Quotient.mk (Ideal.span {ys})
  have hsurj : Function.Surjective (π.comp (algebraMap R S)) := by
    intro s
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective s
    have hs2 : (s : K) ∈ (Polynomial.aeval (R := R) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact s.2
    obtain ⟨f, hf⟩ := hs2
    have hfs : Polynomial.aeval ys f = s :=
      Subtype.ext (by rw [← hf, Polynomial.aeval_subalgebra_coe]; rfl)
    refine ⟨f.coeff 0, ?_⟩
    rw [← hs, ← hfs, RingHom.comp_apply]
    conv_rhs => rw [← Polynomial.X_mul_divX_add f]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ys), zero_mul, zero_add]
  have htop : (IsLocalRing.maximalIdeal R).map (π.comp (algebraMap R S)) = ⊤ := by
    have := congrArg (Ideal.map π) hJ
    rwa [Ideal.map_sup, Ideal.map_map, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1
    (htop ▸ Submodule.mem_top : (1 : S ⧸ Ideal.span {ys}) ∈ _)
  have hmem : ys ∣ algebraMap R S (1 - a) := by
    rw [← Ideal.mem_span_singleton, map_sub, map_one, ← Ideal.Quotient.eq]
    exact ha1.symm
  have hunitA : IsUnit (algebraMap R S (1 - a)) :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).1 ha)).map _
  obtain ⟨u, hu⟩ := isUnit_of_dvd_unit hmem hunitA
  apply hnot
  have h1 : ((u⁻¹ : Sˣ) : S) * ys = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Sˣ) : S) : K) = y⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val h1)
  exact h2 ▸ ((u⁻¹ : Sˣ) : S).2

theorem _root_.GlobalTheory.ValCrit.dvd_of_forall_cdvr : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (p q : R), q ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V),
      _root_.GlobalTheory.LN.CDvr V → Function.Injective φ →
      (IsLocalRing.maximalIdeal V).comap φ = IsLocalRing.maximalIdeal R → φ q ∣ φ p) →
    q ∣ p := by
  intro R _ _ _ _ _ _ p q hq H
  by_cases hp : p = 0
  · exact hp ▸ dvd_zero q
  by_contra hdvd
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hpK : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ hinjK).2 hp
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinjK).2 hq
  set y : K := algebraMap R K q / algebraMap R K p with hy_def
  have hy : y ≠ 0 := div_ne_zero hqK hpK
  set S := Algebra.adjoin R {y}
  have hnot : y⁻¹ ∉ S := by
    intro hmem
    have hint := _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy hmem
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine hdvd ⟨r, hinjK ?_⟩
    rw [map_mul, hr, hy_def, inv_div, mul_comm, div_mul_cancel₀ _ hqK]
  let ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hinjS : Function.Injective (algebraMap R S) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : CharZero S := charZero_of_injective_algebraMap hinjS
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) ⊔ Ideal.span {ys}
  have hJ : J ≠ ⊤ := maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin y hnot
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hyP : ys ∈ P := hJP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self ys))
  have hcomapP : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact (hPmax.isPrime.comap (algebraMap R S)).ne_top
    · exact Ideal.map_le_iff_le_comap.1 (le_trans le_sup_left hJP)
  obtain ⟨V, _, _, _, φ, hV, hφ, hcomap⟩ :=
    _root_.GlobalTheory.PrimeUnif.exists_cdvr S P
  have hψ : Function.Injective (φ.comp (algebraMap R S)) := hφ.comp hinjS
  have hψc : (IsLocalRing.maximalIdeal V).comap (φ.comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.comap_comap, hcomap, hcomapP]
  obtain ⟨v, hv⟩ := H V (φ.comp (algebraMap R S)) hV hψ hψc
  have hrel : ys * algebraMap R S p = algebraMap R S q := by
    apply Subtype.ext
    change y * algebraMap R K p = algebraMap R K q
    rw [hy_def, div_mul_cancel₀ _ hpK]
  have hψp : φ (algebraMap R S p) ≠ 0 := by
    intro h0
    exact hp (hψ (by simpa using h0))
  have hone : φ ys * v = 1 := by
    apply mul_left_cancel₀ hψp
    simp only [RingHom.comp_apply] at hv
    rw [← hrel, map_mul] at hv
    calc φ (algebraMap R S p) * (φ ys * v) = φ ys * φ (algebraMap R S p) * v := by ring
      _ = φ (algebraMap R S p) := hv.symm
      _ = φ (algebraMap R S p) * 1 := (mul_one _).symm
  have hunit : IsUnit (φ ys) := isUnit_iff_exists_inv.2 ⟨v, hone⟩
  have hys : ys ∉ P := by
    rw [← hcomap, Ideal.mem_comap]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hunit
  exact hys hyP

end GlobalTheory.ValCrit
