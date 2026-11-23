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
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinateQuotientRegular
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularQuotientPrimeElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactorsStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AssociatedOfHeightOneAgree
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtUnit

theorem unit_mul_monomial_of_forall_height_one (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (x : K) (hx : x ≠ 0)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ x * algebraMap R K d = algebraMap R K c) :
    ∃ (u : Rˣ) (m : Fin n → ℤ), x = algebraMap R K u * ∏ j ∈ J, (algebraMap R K (π j)) ^ m j := by
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0' : b0 ≠ 0 := nonZeroDivisors.ne_zero hb0
  have hb0K : algebraMap R K b0 ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0'
  have ha0 : a0 ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨α, a, ha, hna⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J a0 ha0
  obtain ⟨β, b, hb, hnb⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J b0 hb0'
  have hπ0 : ∀ j ∈ J, π j ≠ 0 := fun j hj =>
    (hπ j hj).elim (fun hu => hu.ne_zero) (fun hp => hp.ne_zero)
  have han : a ≠ 0 := by rintro rfl; rw [zero_mul] at ha; exact ha0 ha
  have hbn : b ≠ 0 := by rintro rfl; rw [zero_mul] at hb; exact hb0' hb
  have hprodQ : ∀ (Q : Ideal R), Q.IsPrime → (∀ j ∈ J, π j ∉ Q) →
      ∀ e : Fin n → ℕ, ∏ j ∈ J, π j ^ e j ∉ Q := by
    intro Q hQ hQJ e hmem
    obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.associated_of_height_one_agree R π J a b han hbn hπ
    (fun j hj hp => ⟨hna j hj hp, hnb j hj hp⟩) (fun Q hQ h1 hQJ => by
      obtain ⟨c, d, hc, hd, hcd⟩ := h Q hQ h1 hQJ
      refine ⟨c * ∏ j ∈ J, π j ^ β j, d * ∏ j ∈ J, π j ^ α j,
        hQ.mul_notMem hc (hprodQ Q hQ hQJ β), hQ.mul_notMem hd (hprodQ Q hQ hQJ α), ?_⟩
      have e1 : algebraMap R K a0 * algebraMap R K d = algebraMap R K b0 * algebraMap R K c := by
        rw [← hcd]; field_simp
      have e2 : a0 * d = b0 * c := IsFractionRing.injective R K (by rw [map_mul, map_mul, e1])
      rw [ha, hb] at e2
      linear_combination e2)
  refine ⟨u, fun j => (α j : ℤ) - β j, ?_⟩
  have hK : ∀ j ∈ J, algebraMap R K (π j) ≠ 0 := fun j hj => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ0 j hj
  have hprodK : ∏ j ∈ J, algebraMap R K (π j) ^ ((α j : ℤ) - β j) =
      (∏ j ∈ J, algebraMap R K (π j) ^ α j) / ∏ j ∈ J, algebraMap R K (π j) ^ β j := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [zpow_sub₀ (hK j hj), zpow_natCast, zpow_natCast]
  have hβK : ∏ j ∈ J, algebraMap R K (π j) ^ β j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hK j hj)
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hbn
  rw [hprodK, ha, hb, hu]
  simp only [map_mul, map_prod, map_pow]
  field_simp

theorem unit_mul_monomial_iff : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  intro p _ A _ _ _ n t het P _ L _ _ _ J ht g
  constructor
  · intro hL
    letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A :=
      (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := het
    haveI : IsRegularRing A := GlobalTheory.isRegularRing_of_etale (MvPolynomial (Fin n) (ZMod p)) A
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      IsRegularRing.isRegularLocalRing_localization P
    obtain ⟨hRd, hRi⟩ :=
      GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime P)
    haveI : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      rintro h0
      exact y.2 (h0 ▸ P.zero_mem)
    letI : Algebra (Localization.AtPrime P) L := (IsLocalization.lift hunits).toAlgebra
    haveI : IsScalarTower A (Localization.AtPrime P) L :=
      IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunits a).symm)
    haveI : IsFractionRing (Localization.AtPrime P) L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ L
    have hprime : ∀ j ∈ J, IsUnit (algebraMap A (Localization.AtPrime P) (t j)) ∨
        Prime (algebraMap A (Localization.AtPrime P) (t j)) := by
      intro j hj
      by_cases hjP : t j ∈ P
      · right
        refine GlobalTheory.T.regular_quotient_prime_element A P (t j) (fun h0 => ht j (by rw [h0, map_zero])) hjP
          (GlobalTheory.T.etale_coordinate_quotient_regular p A t het j)
      · left
        exact IsLocalization.map_units (Localization.AtPrime P) (⟨t j, hjP⟩ : P.primeCompl)
    obtain ⟨u, m, hum⟩ := unit_mul_monomial_of_forall_height_one (Localization.AtPrime P) L
      (fun j => algebraMap A (Localization.AtPrime P) (t j)) J hprime (g : L) g.ne_zero (by
        intro Q hQ _ hQJ
        have hQ'P : Q.comap (algebraMap A (Localization.AtPrime P)) ≤ P := by
          intro x hx
          by_contra hxP
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl)))
        obtain ⟨a, b, ha, hb, hab⟩ := hL (Q.comap (algebraMap A (Localization.AtPrime P)))
          (Ideal.comap_isPrime _ Q) hQ'P (fun j hj hjQ => hQJ j hj hjQ)
        refine ⟨algebraMap A _ a, algebraMap A _ b, ha, hb, ?_⟩
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact hab)
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective P.primeCompl (u : Localization.AtPrime P)
    change IsLocalization.mk' (Localization.AtPrime P) a s = _ at has
    have haP : a ∈ P.primeCompl := by
      rw [← IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P a s, has]
      exact u.isUnit
    refine ⟨Units.map (algebraMap (Localization.AtPrime P) L : Localization.AtPrime P →* L) u, m,
      ⟨a, s, haP, s.2, ?_⟩, ?_⟩
    · rw [Units.coe_map, MonoidHom.coe_coe, ← has, IsScalarTower.algebraMap_apply A
        (Localization.AtPrime P) L s, IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L a,
        ← map_mul, IsLocalization.mk'_spec]
    · ext
      rw [hum, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨u, m, ⟨a, b, ha, hb, hab⟩, rfl⟩ Q hQ hQP hQJ
    have hK : ∀ j, algebraMap A L (t j) ≠ 0 := ht
    have hprodQ : ∀ e : Fin n → ℕ, ∏ j ∈ J, t j ^ e j ∉ Q := by
      intro e hmem
      obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
    refine ⟨a * ∏ j ∈ J, t j ^ (m j).toNat, b * ∏ j ∈ J, t j ^ (-m j).toNat,
      hQ.mul_notMem (fun h => ha (hQP h)) (hprodQ _),
      hQ.mul_notMem (fun h => hb (hQP h)) (hprodQ _), ?_⟩
    have key : ∀ j, algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat =
        algebraMap A L (t j) ^ (m j).toNat := by
      intro j
      have e : m j = ((m j).toNat : ℤ) - ((-m j).toNat : ℤ) := (Int.toNat_sub_toNat_neg _).symm
      calc algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat
          = algebraMap A L (t j) ^ (((m j).toNat : ℤ) - ((-m j).toNat : ℤ)) *
            algebraMap A L (t j) ^ (-m j).toNat := by rw [← e]
        _ = _ := by
          rw [zpow_sub₀ (hK j), zpow_natCast, zpow_natCast,
            div_mul_cancel₀ _ (pow_ne_zero _ (hK j))]
    rw [Units.val_mul, Units.coe_prod, map_mul, map_mul, map_prod, map_prod, ← hab]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow]
    rw [show (u : L) * (∏ j ∈ J, algebraMap A L (t j) ^ m j) *
        (algebraMap A L b * ∏ j ∈ J, algebraMap A L (t j) ^ (-m j).toNat) =
        (u : L) * algebraMap A L b * ∏ j ∈ J, (algebraMap A L (t j) ^ m j *
          algebraMap A L (t j) ^ (-m j).toNat) by rw [Finset.prod_mul_distrib]; ring]
    simp only [key]

end GlobalTheory.EtUnit
