import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem ringKrullDim_le_of_hasGoingDown {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.HasGoingDown A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  obtain ⟨P, -, hP, hlo⟩ := (maximalIdeal B).exists_ideal_le_liesOver_of_le
    (p := l.last.asIdeal) (q := maximalIdeal A) (le_maximalIdeal l.last.2.ne_top)
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  exact le_iSup_of_le L (by rw [hlen])

theorem IsRegularLocalRing.of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [IsRegularLocalRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← h]
  calc (((maximalIdeal A).map (algebraMap A B)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal A).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing
    _ = ringKrullDim A := (isRegularLocalRing_iff A).mp inferInstance
    _ ≤ ringKrullDim B := ringKrullDim_le_of_hasGoingDown

theorem isRegularLocalRing_localization_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  apply IsRegularLocalRing.of_flat_of_map_maximalIdeal (A := Localization.AtPrime p)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hmap

theorem isRegularRing_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth (R := k) (S := A)
  obtain ⟨f, hfs, hfq⟩ : ∃ f ∈ s, f ∉ q := by
    by_contra! hc
    exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
  obtain ⟨q', hq', hcomap⟩ : ∃ q' : Ideal (Localization.Away f), q'.IsPrime ∧
      q'.comap (algebraMap A (Localization.Away f)) = q := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) f).mpr hfq
    exact ⟨q.map (algebraMap A (Localization.Away f)),
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ q hq hdisj,
      IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ hq hdisj⟩
  subst hcomap
  suffices IsRegularLocalRing (Localization.AtPrime q') from
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q').toRingEquiv.symm
  have hf := hstd f hfs
  obtain ⟨n, g, -, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap k (Localization.Away f))
    (RingHom.isStandardSmooth_algebraMap.mpr hf)
  algebraize [g]
  exact isRegularLocalRing_localization_of_etale (P := MvPolynomial (Fin n) k) q'

theorem isRegularLocalRing_localization_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  have := isRegularRing_of_smooth k A
  inferInstance

theorem isRegularRing_of_smooth_field (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsRegularRing A :=
  isRegularRing_of_smooth k A

theorem isDomain_localization_of_smooth (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  have := isRegularLocalRing_localization_of_smooth k A q
  IsRegularLocalRing.isDomain

open AlgebraicGeometry CategoryTheory

theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {R : CommRingCat.{u}} [IsRegularRing R]
    (f : X ⟶ Spec R) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsm : (f.appLE ⊤ U (by simp)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have : IsRegularRing Γ(Spec R, ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  set P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hreg : IsRegularLocalRing (Localization.AtPrime P) :=
    isRegularLocalRing_localization_of_smooth Γ(Spec R, ⊤) Γ(X, U) P
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, U)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv

theorem isRegularLocalRing_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth f x

theorem isDomain_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) :=
  have := isRegularLocalRing_stalk_of_smooth_field f x
  IsRegularLocalRing.isDomain

end GroundTheory.Arith.SchemeCoh
