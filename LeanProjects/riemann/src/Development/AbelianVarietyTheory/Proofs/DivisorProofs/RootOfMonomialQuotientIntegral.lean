import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem not_X_dvd_X {K : Type} [Field K] {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    ¬ (X i : MvPolynomial (Fin n) K) ∣ X k := by
  rintro ⟨q, hq⟩
  have := congrArg (MvPolynomial.eval (fun j => if j = i then (0 : K) else 1)) hq
  simp [hik.symm] at this

theorem prod_X_dvd_of_dvd_X_mul {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    ∀ (S : Finset (Fin n)), k ∉ S → ∀ h : MvPolynomial (Fin n) K,
      (∏ j ∈ S, X j) ∣ X k * h → (∏ j ∈ S, X j) ∣ h := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert i S hi ih =>
    intro hk h hd
    rw [Finset.prod_insert hi] at hd ⊢
    have hik : i ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hXi : (X i : MvPolynomial (Fin n) K) ∣ h := by
      rcases (X_prime (R := K) (i := i)).dvd_or_dvd (dvd_trans (dvd_mul_right _ _) hd) with h1 | h1
      · exact absurd h1 (not_X_dvd_X hik)
      · exact h1
    obtain ⟨h', rfl⟩ := hXi
    have hd' : X i * (∏ j ∈ S, X j) ∣ X i * (X k * h') := by
      rw [mul_left_comm (X i) (X k) h']; exact hd
    have h2 := (mul_dvd_mul_iff_left (X_ne_zero (R := K) i)).1 hd'
    exact mul_dvd_mul_left _ (ih (fun h => hk (Finset.mem_insert_of_mem h)) h' h2)

theorem prod_X_dvd_of_dvd_X_pow_mul {K : Type} [Field K] {n : ℕ} (k : Fin n)
    (S : Finset (Fin n)) (hk : k ∉ S) :
    ∀ (e : ℕ) (h : MvPolynomial (Fin n) K), (∏ j ∈ S, X j) ∣ X k ^ e * h → (∏ j ∈ S, X j) ∣ h := by
  intro e
  induction e with
  | zero => intro h hd; simpa using hd
  | succ e ih =>
    intro h hd
    apply ih
    apply prod_X_dvd_of_dvd_X_mul k S hk
    rwa [pow_succ, mul_comm _ (X k), mul_assoc] at hd

theorem prod_X_dvd_of_dvd_pow {K : Type} [Field K] {n : ℕ} :
    ∀ (S : Finset (Fin n)) (f : MvPolynomial (Fin n) K) (m : ℕ),
      (∏ j ∈ S, X j) ∣ f ^ m → (∏ j ∈ S, X j) ∣ f := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert k S hk ih =>
    intro f m hd
    rw [Finset.prod_insert hk] at hd ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at hd
      exact dvd_trans hd (one_dvd _)
    have hXk : (X k : MvPolynomial (Fin n) K) ∣ f :=
      (X_prime (R := K) (i := k)).dvd_of_dvd_pow (dvd_trans (dvd_mul_right _ _) hd)
    obtain ⟨f', rfl⟩ := hXk
    have h1 : (∏ j ∈ S, X j) ∣ X k ^ m * f' ^ m := by
      rw [← mul_pow]; exact dvd_trans (dvd_mul_left _ _) hd
    exact mul_dvd_mul_left _ (ih f' m (prod_X_dvd_of_dvd_X_pow_mul k S hk m _ h1))

theorem isRadical_span_prod_X {K : Type} [Field K] {n : ℕ} (S : Finset (Fin n)) :
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) K)}).IsRadical := by
  intro y hy
  obtain ⟨e, he⟩ := (Ideal.mem_radical_iff).1 hy
  rw [Ideal.mem_span_singleton] at he ⊢
  exact prod_X_dvd_of_dvd_pow S y e he

end GlobalTheory.EtRoot

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem dvd_of_dvd_pow_prod_coords (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (S : Finset (Fin n))
    (z : A) (k : ℕ) (hz : (∏ j ∈ S, t j) ∣ z ^ k) : (∏ j ∈ S, t j) ∣ z := by
  letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := he
  have h1 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := A)
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) (ZMod p))}) (isRadical_span_prod_X S)
  rw [Ideal.map_span, Set.image_singleton] at h1
  have h2 : algebraMap (MvPolynomial (Fin n) (ZMod p)) A (∏ j ∈ S, X j) = ∏ j ∈ S, t j := by
    rw [RingHom.algebraMap_toAlgebra, map_prod]
    simp
  rw [h2] at h1
  have hmem : z ∈ (Ideal.span {∏ j ∈ S, t j}).radical :=
    (Ideal.mem_radical_iff).2 ⟨k, Ideal.mem_span_singleton.2 hz⟩
  exact Ideal.mem_span_singleton.1 (h1 hmem)

theorem mem_local_of_pow_mem (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (P : Ideal A) [P.IsPrime]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (x : L) (m : ℕ) (hm : 0 < m)
    (hx : ∃ a b : A, b ∉ P ∧ x ^ m * algebraMap A L b = algebraMap A L a) :
    ∃ a b : A, b ∉ P ∧ x * algebraMap A L b = algebraMap A L a := by
  let Q := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra Q A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale Q A := he
  let T := Localization.AtPrime P
  haveI : Algebra.FormallyEtale Q T := inferInstance
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T P.primeCompl
  haveI : Algebra.EssFiniteType Q T := Algebra.EssFiniteType.comp Q A T
  haveI : IsIntegrallyClosed Q := isIntegrallyClosed_mvPolynomial_fin (ZMod p) n
  obtain ⟨_, hT⟩ := GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale Q T
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
    have hy : (y : A) ≠ 0 := fun h => y.2 (h ▸ P.zero_mem)
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hy)
  letI : Algebra T L := (IsLocalization.lift (M := P.primeCompl) (S := T) hunit).toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq
    (fun y => (IsLocalization.lift_eq (M := P.primeCompl) (S := T) hunit y).symm)
  haveI : IsFractionRing T L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl T L
  have hmk : ∀ (a : A) (b : P.primeCompl),
      algebraMap T L (IsLocalization.mk' T a b) * algebraMap A L b = algebraMap A L a := by
    intro a b
    rw [IsScalarTower.algebraMap_apply A T L b, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, b, hb, hab⟩ := hx
  have hbL : algebraMap A L b ≠ 0 := (hunit ⟨b, hb⟩).ne_zero
  have hxm : x ^ m = algebraMap T L (IsLocalization.mk' T a (⟨b, hb⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hbL
    rw [hab]; exact (hmk a ⟨b, hb⟩).symm
  have hint : IsIntegral T x := by
    apply IsIntegral.of_pow hm
    rw [hxm]; exact isIntegral_algebraMap
  obtain ⟨u, hu⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := L)).1 hint
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl u
  refine ⟨c, s, s.2, ?_⟩
  rw [← hu]; exact hmk c s

theorem div_prod_coords_mem_of_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  intro p _ A _ _ _ n t he P _ L _ _ _ S g m hm ⟨a, b, hb, hab⟩
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  by_cases h0 : (∏ j ∈ S, t j) = 0
  · exact ⟨0, 1, h1P, by simp [h0]⟩
  have hπL : algebraMap A L (∏ j ∈ S, t j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 h0
  have h1 : ∃ a' b' : A, b' ∉ P ∧ g ^ m * algebraMap A L b' = algebraMap A L a' :=
    ⟨a * ∏ j ∈ S, t j, b, hb, by
      rw [map_mul, ← hab, div_mul_eq_mul_div, div_mul_cancel₀ _ hπL]⟩
  obtain ⟨x, s, hs, hxs⟩ := mem_local_of_pow_mem p A t he P L g m hm h1
  have hbs : s * b ∉ P := fun h => ((‹P.IsPrime›).mem_or_mem h).elim hs hb
  have h2 : x ^ m * b = a * (∏ j ∈ S, t j) * s ^ m := by
    apply IsFractionRing.injective A L
    simp only [map_mul, map_pow]
    rw [← hxs, ← hab]
    field_simp
    ring
  have h3 : (∏ j ∈ S, t j) ∣ (x * b) ^ m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨a * s ^ (k + 1) * b ^ k, ?_⟩
    calc (x * b) ^ (k + 1) = (x ^ (k + 1) * b) * b ^ k := by ring
      _ = _ := by rw [h2]; ring
  obtain ⟨y, hy⟩ := dvd_of_dvd_pow_prod_coords p A t he S (x * b) m h3
  refine ⟨y, s * b, hbs, ?_⟩
  have h4 : algebraMap A L (x * b) = algebraMap A L (∏ j ∈ S, t j) * algebraMap A L y := by
    rw [hy, map_mul]
  rw [map_mul, ← hxs] at h4
  rw [map_mul, div_mul_eq_mul_div, div_eq_iff hπL]
  linear_combination h4

end GlobalTheory.EtRoot
