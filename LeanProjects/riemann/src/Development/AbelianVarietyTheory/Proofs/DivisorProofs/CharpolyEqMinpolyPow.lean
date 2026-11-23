import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec

open CategoryTheory Polynomial
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.CharpolyMinpolyPower

theorem eq_pow_of_roots (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (P m : ℚ[X]) (hP : P.Monic)
    (hm : m.Monic) (hirr : Irreducible m) (h : ∀ a : Ω, aeval a P = 0 → minpoly ℚ a = m) :
    ∃ k : ℕ, P = m ^ k := by
  suffices H : ∀ n : ℕ, ∀ Q : ℚ[X], Q.natDegree = n → Q.Monic →
      (∀ a : Ω, aeval a Q = 0 → minpoly ℚ a = m) → ∃ k : ℕ, Q = m ^ k from H _ P rfl hP h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hQ hroots
    by_cases hn : Q.natDegree = 0
    · exact ⟨0, by rw [pow_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hQ hn⟩
    · have hdeg : Q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hQ.ne_zero]
        exact_mod_cast hn
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero Ω Q hdeg
      have hdvd : m ∣ Q := hroots a ha ▸ minpoly.dvd ℚ a ha
      obtain ⟨Q', rfl⟩ := hdvd
      have hQ' : Q'.Monic := hm.of_mul_monic_left hQ
      have hsum : (m * Q').natDegree = m.natDegree + Q'.natDegree := hm.natDegree_mul hQ'
      have hm0 : 0 < m.natDegree := hirr.natDegree_pos
      obtain ⟨k, hk⟩ := ih Q'.natDegree (by omega) Q' rfl hQ'
        (fun b hb => hroots b (by rw [map_mul, hb, mul_zero]))
      exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

theorem deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : NumberField.RingOfIntegers F →+* End A) (r : NumberField.RingOfIntegers F) (hr : r ≠ 0) :
    deg (A := A) (B := A) (ι r) ≠ 0 := by
  have hI : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.absNorm (Ideal.span {r}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
  have hc : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN0
  have hι : ι r ≫ ι s = ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • 𝟙 A := by
    rw [← End.mul_def, ← map_mul, hs, map_natCast, natCast_zsmul]
    exact (nsmul_one (A := End A) _).symm
  obtain ⟨-, hdN⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hc
  have hcomp := (isIsogeny_comp_iff_and_deg_comp K A A A (ι r) (ι s) rfl rfl).2
  rw [hι, hdN] at hcomp
  intro h0
  rw [h0, zero_mul] at hcomp
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hc) hcomp

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : NumberField.RingOfIntegers F →+* End A) (x : NumberField.RingOfIntegers F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  obtain ⟨hcp, -⟩ := charpoly_spec K A (ι x)
  obtain ⟨hmon, hdeg, -⟩ := hcp
  have hPm : ((charpoly (ι x)).map (Int.castRingHom ℚ)).Monic := hmon.map _
  have hPdeg : ((charpoly (ι x)).map (Int.castRingHom ℚ)).natDegree = 2 * A.dim := by
    rw [hmon.natDegree_map, hdeg]
  let ιa : NumberField.RingOfIntegers F →ₐ[ℤ] End A :=
    AlgHom.mk ι (fun n => by
      show ι (algebraMap ℤ _ n) = algebraMap ℤ (End A) n
      rw [eq_intCast (algebraMap ℤ (NumberField.RingOfIntegers F)), eq_intCast (algebraMap ℤ (End A))]
      exact map_intCast ι n)
  have hxint : IsIntegral ℚ (x : F) := Algebra.IsIntegral.isIntegral _
  have key : ∀ a : AlgebraicClosure ℚ, aeval a ((charpoly (ι x)).map (Int.castRingHom ℚ)) = 0 →
      minpoly ℚ a = minpoly ℚ (x : F) := by
    intro a ha
    have haint : IsIntegral ℚ a := IsAlgebraic.isIntegral ⟨_, hPm.ne_zero, ha⟩
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ a)
    have hRa : aeval a (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) _ (minpoly.aeval ℚ a)
    have hprod := deg_aeval_eq_prod_aroots K A (ι x) (AlgebraicClosure ℚ)
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))
    have hmem : a ∈ ((charpoly (ι x)).map (Int.castRingHom ℚ)).aroots (AlgebraicClosure ℚ) :=
      (Polynomial.mem_aroots).2 ⟨hPm.ne_zero, ha⟩
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, hmem, hRa⟩)] at hprod
    have hdeg0 : deg (A := A) (B := A) (aeval (ι x)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) = 0 := by
      have h := (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).1 hprod
      exact_mod_cast h
    rw [show aeval (ι x) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) =
        ι (aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) from
      Polynomial.aeval_algHom_apply ιa x _] at hdeg0
    have hRx : aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      by_contra hne
      exact deg_ne_zero A ι _ hne hdeg0
    have hRxF : aeval (x : F) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      have h := congrArg (algebraMap (NumberField.RingOfIntegers F) F) hRx
      rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h
    have hqx : aeval (x : F) (minpoly ℚ a) = 0 := by
      have h1 : aeval (x : F) ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
          (minpoly ℚ a)).map (algebraMap ℤ ℚ)) = 0 := by
        rwa [Polynomial.aeval_map_algebraMap]
      rw [hb, map_zsmul] at h1
      exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero hbM)
    exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hqx (minpoly.monic haint)
  obtain ⟨k, hk⟩ := eq_pow_of_roots (AlgebraicClosure ℚ) _ _ hPm (minpoly.monic hxint)
    (minpoly.irreducible hxint) key
  refine ⟨k, Nat.pos_of_ne_zero ?_, hk⟩
  rintro rfl
  rw [hk, pow_zero, Polynomial.natDegree_one] at hPdeg
  omega

end GlobalTheory.CharpolyMinpolyPower
