import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory.EtaleSpreadReg

theorem isDedekindDomain_atPrime (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  have : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun {P} hP hPp => Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP hPp⟩
  exact {}

theorem isRegularLocalRing_polynomial_atPrime (A : Type*) [CommRing A] (Q₀ : Ideal A[X])
    [Q₀.IsPrime] [IsRegularRing (Localization.AtPrime (Q₀.under A))] :
    IsRegularLocalRing (Localization.AtPrime Q₀) := by
  set p : Ideal A := Q₀.under A with hpdef
  let Ap := Localization.AtPrime p
  letI : Algebra A[X] Ap[X] := Polynomial.algebra A Ap
  let M : Submonoid A[X] := Submonoid.map C p.primeCompl
  haveI : IsLocalization M Ap[X] := Polynomial.isLocalization p.primeCompl Ap
  have hdisj : Disjoint (M : Set A[X]) (Q₀ : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  let Q' : Ideal Ap[X] := Q₀.map (algebraMap A[X] Ap[X])
  haveI hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Ap[X] Q₀ inferInstance hdisj
  have hc : Q'.comap (algebraMap A[X] Ap[X]) = Q₀ :=
    IsLocalization.comap_map_of_isPrime_disjoint M Ap[X] inferInstance hdisj
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q') Q'
  have e : (Q'.comap (algebraMap A[X] Ap[X])).primeCompl = Q₀.primeCompl := by
    ext x; simp only [Ideal.mem_primeCompl_iff, hc]
  have h2 : IsLocalization Q₀.primeCompl (Localization.AtPrime Q') := by
    rw [← e]; exact h
  have hreg : IsRegularLocalRing (Localization.AtPrime Q') := isRegularRing_iff.mp inferInstance Q'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q₀.primeCompl (Localization.AtPrime Q') (Localization.AtPrime Q₀)).toRingEquiv

theorem isRegularLocalRing_atPrime_of_etale (S T : Type*) [CommRing S] [IsNoetherianRing S]
    [CommRing T] [Algebra S T] [Algebra.Etale S T] (q : Ideal T) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.under S))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  let p : Ideal S := q.under S
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hun : Algebra.IsUnramifiedAt S q := inferInstance
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq S p q).mp hun).2
  have hm' : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← hm, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := Ideal.spanFinrank_map_le_of_fg
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
  rw [hm'] at h1
  have h2 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  refine le_trans ?_ (WithBot.coe_le_coe.mpr h2)
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    ← hreg.spanFinrank_maximalIdeal]
  exact_mod_cast h1

theorem isRegularLocalRing_atPrime :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _ P _ hP
  let Q : Ideal EA := P.comap (algebraMap EA (Localization.AtPrime QA))
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization QA.primeCompl
      (Localization.AtPrime P) P
  have hpe : (Q.under (Polynomial A)).under A = P.comap (algebraMap A (Localization.AtPrime QA)) := by
    rw [Ideal.under_under]
    show Ideal.comap (algebraMap A EA) (Ideal.comap (algebraMap EA (Localization.AtPrime QA)) P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  haveI : IsDedekindDomain (Localization.AtPrime ((Q.under (Polynomial A)).under A)) :=
    isDedekindDomain_atPrime A _ (hpe ▸ hP)
  have h0 := isRegularLocalRing_polynomial_atPrime A (Q.under (Polynomial A))
  have h1 := isRegularLocalRing_atPrime_of_etale (Polynomial A) EA Q h0
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime P)).toRingEquiv

end GlobalTheory.EtaleSpreadReg
