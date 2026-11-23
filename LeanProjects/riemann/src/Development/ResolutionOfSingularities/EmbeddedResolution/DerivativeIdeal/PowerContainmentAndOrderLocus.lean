import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem support_subset_orderAtLeastLocus_of_le_pow {X : Scheme.{u}} (Z I : X.IdealSheafData) (m : ℕ)
    (h : I ≤ Z ^ m) : (Z.support : Set X) ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow]
  have h1 : stalkIdeal I x ≤ stalkIdeal (Z ^ m) x := stalkIdeal_mono h x
  rw [stalkIdeal_pow] at h1
  refine h1.trans (Ideal.pow_right_mono ?_ m)
  exact (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx

private theorem mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen {X : Scheme.{u}} (I : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
  constructor
  · intro hle y hy
    have h2 : (X.presheaf.germ U (x : X) x.2).hom y ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk (x : X)) := hle (Ideal.mem_map_of_mem _ hy)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mp h2
  · intro hle
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mpr (hle hy)

private theorem exists_point_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = q := by
  have hmem : hU.fromSpec.base q ∈ U := by
    have h1 : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  refine ⟨⟨hU.fromSpec.base q, hmem⟩, ?_⟩
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  apply hinj
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base q, hmem⟩

private theorem notMem_primeIdealOf_of_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (g : Γ(X, U)) (x : U) (hxg : (x : X) ∈ X.basicOpen g) :
    g ∉ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  have hunit : IsUnit ((X.presheaf.germ U (x : X) x.2).hom g) :=
    (X.mem_basicOpen g (x : X) x.2).mp hxg
  intro hmem
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal g).mpr hmem
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hunit

private theorem ideal_le_of_support_subset {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (Z J : X.IdealSheafData) (hrad : (Z.ideal ⟨U, hU⟩).IsRadical)
    (hsupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ J.support) :
    J.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
  have hrad' : (Z.ideal ⟨U, hU⟩).radical = Z.ideal ⟨U, hU⟩ := hrad.radical
  rw [← hrad', Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq1, hq2⟩
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq hU ⟨q, hq2⟩
  have hxq' : (hU.primeIdealOf x).asIdeal = q := congrArg PrimeSpectrum.asIdeal hxq
  have hxZ : (x : X) ∈ Z.support := by
    refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z hU x).mpr ?_
    rw [hxq']
    exact hq1
  have hxJ := hsupp (x : X) hxZ x.2
  have hfin := (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen J hU x).mp hxJ
  rw [hxq'] at hfin
  exact hfin

private theorem ideal_eq_top_of_disjoint_support {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : X.affineOpens) (hW : ∀ y : X, y ∈ W.1 → y ∉ Z.support) : Z.ideal W = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have : P.IsPrime := hP.isPrime
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq W.2 ⟨P, hP.isPrime⟩
  have hxq' : (W.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
  refine hW (x : X) x.2 ?_
  refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z W.2 x).mpr ?_
  rw [hxq']
  exact hle

private theorem le_pow_of_forall_le_pow_basicOpen {X : Scheme.{u}} (Z I : X.IdealSheafData) (m : ℕ)
    (hloc : ∀ (V : X.affineOpens) (x : X), x ∈ V.1 →
      ∃ g : Γ(X, V.1), x ∈ X.basicOpen g ∧
        I.ideal (X.affineBasicOpen g) ≤ Z.ideal (X.affineBasicOpen g) ^ m) :
    I ≤ Z ^ m := by
  have key : ∀ V : X.affineOpens, I.ideal V ≤ (Z ^ m).ideal V := by
    intro V
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    intro a ha
    by_contra hcon
    have hcol : ((Z.ideal V) ^ m).colon (Ideal.span {a}) ≠ ⊤ := by
      intro htop
      have h1 : (1 : Γ(X, V.1)) ∈ ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
        rw [htop]; exact Submodule.mem_top
      have h2 := Submodule.mem_colon.mp h1 a (Ideal.mem_span_singleton_self a)
      rw [smul_eq_mul, one_mul] at h2
      exact hcon h2
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_le_maximal _ hcol
    have : P.IsPrime := hP.isPrime
    obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq V.2 ⟨P, hP.isPrime⟩
    have hxq' : (V.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
    obtain ⟨g, hxg, hgle⟩ := hloc V (x : X) x.2
    have hgP : g ∉ P := by
      have hg := notMem_primeIdealOf_of_mem_basicOpen V.2 g x hxg
      rw [hxq'] at hg
      exact hg
    let _ : Algebra Γ(X, V.1) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
    have hI : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (I.ideal V) =
        I.ideal (X.affineBasicOpen g) := I.map_ideal_basicOpen V g
    have hZ : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (Z.ideal V) =
        Z.ideal (X.affineBasicOpen g) := Z.map_ideal_basicOpen V g
    have hmem : (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) a ∈
        Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) ((Z.ideal V) ^ m) := by
      rw [Ideal.map_pow, hZ]
      exact hgle (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)] at hmem
    obtain ⟨⟨bb, sm⟩, heq⟩ := hmem
    rw [← map_mul] at heq
    obtain ⟨tm, hct⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g)
      Γ(X, X.basicOpen g)).mp heq
    have hmemB : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a ∈ (Z.ideal V) ^ m := by
      have h3 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a
          = (tm : Γ(X, V.1)) * (a * (sm : Γ(X, V.1))) := by ring
      rw [h3, hct]
      exact Ideal.mul_mem_left _ _ bb.2
    have hcolmem : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) ∈
        ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
      refine Submodule.mem_colon.mpr ?_
      intro q hq
      obtain ⟨cc, rfl⟩ := Ideal.mem_span_singleton'.mp hq
      have h4 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) • (cc * a)
          = cc * (((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a) := by
        rw [smul_eq_mul]; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ hmemB
    obtain ⟨i, hi⟩ := tm.2
    obtain ⟨j, hj⟩ := sm.2
    have hts : (tm : Γ(X, V.1)) * (sm : Γ(X, V.1)) = g ^ (i + j) := by
      rw [← hi, ← hj, pow_add]
    have hmemP : g ^ (i + j) ∈ P := hts ▸ hPle hcolmem
    exact hgP (hP.isPrime.mem_of_pow_mem _ hmemP)
  exact key

private theorem isUnit_natCast_of_algebra_of_charZero (k : Type*) [Field k] [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] {r : ℕ} (hr : 1 ≤ r) : IsUnit ((r : ℕ) : R) := by
  have h0 : ((r : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((r : ℕ) : R) = algebraMap k R ((r : ℕ) : k) := (map_natCast (algebraMap k R) r).symm
  rw [h1]
  exact IsUnit.map (algebraMap k R) (IsUnit.mk0 ((r : ℕ) : k) h0)

theorem isRadical_ideal_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (Z : X.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    (Z.ideal ⟨U, hU⟩).IsRadical := by
  classical
  have hmap : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k n S) = Z.ideal ⟨U, hU⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h
  have hg := etale_quotientMk_comp_renameCompl k n S c.coordRingHom (c.coordRingHom_etale hU)
    (Z.ideal ⟨U, hU⟩) hmap.symm
  let _ : Algebra (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
    RingHom.toAlgebra
      (((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp (renameCompl k n S).toRingHom)
  have : Algebra.Etale (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := hg
  have hred : IsReduced (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := by
    refine isReduced_ofLocalizationMaximal _ ?_
    intro q hq
    have : q.IsPrime := hq.isPrime
    have := isRegularLocalRing_localization_atPrime_etale k (n - S.card)
      (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) q
    have : IsDomain (Localization.AtPrime q) := inferInstance
    exact ⟨fun x hx => hx.eq_zero⟩
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr hred

theorem ideal_le_pow_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (Z : X.IdealSheafData)
    (S : Finset (Fin n)) (h : restrictIdeal Z U = c.coordIdeal S) (m : ℕ)
    (I : X.IdealSheafData)
    (hord : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus I m) :
    I.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ ^ m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    rw [pow_zero, Ideal.one_eq_top]
    exact le_top
  let algR : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have htower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have hfet : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let xs : {i : Fin n // i ∈ S} → Γ(X, U) := fun i => c.coord i.1
  let Ds : {i : Fin n // i ∈ S} → Derivation k Γ(X, U) Γ(X, U) :=
    fun i => EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1)
  have hD : ∀ i j : {i : Fin n // i ∈ S}, Ds i (xs j) = if i = j then 1 else 0 := by
    intro i j
    show (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1))
        (c.coord j.1) = if i = j then 1 else 0
    rw [← c.etaleCoordinates_coord j.1, EtaleCoordinates.partialDeriv_coord]
    have hiff : (ULift.up.{u} i.1 = ULift.up.{u} j.1) ↔ i = j := by
      constructor
      · intro hh
        exact Subtype.ext (congrArg ULift.down hh)
      · intro hh
        rw [hh]
    by_cases hij : i = j
    · rw [if_pos (hiff.mpr hij), if_pos hij]
    · rw [if_neg (fun hh => hij (hiff.mp hh)), if_neg hij]
  have hrange : Set.range xs = c.coord '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Ideal.span (Set.range xs) = Z.ideal ⟨U, hU⟩ := by
    rw [hrange, c.ideal_eq_span_coord hU Z S h]
  have hunit : ∀ r : ℕ, 1 ≤ r → IsUnit ((r : ℕ) : Γ(X, U)) := by
    intro r hr
    exact isUnit_natCast_of_algebra_of_charZero k Γ(X, U) hr
  have hbase : derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ := by
    have h1 : (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
      refine ideal_le_of_support_subset hU Z (derivIdealSheafIterate k p (m - 1) I)
        (isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hU c Z S h) ?_
      intro y hy hyU
      have h2 : ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m :=
        support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
      have h3 : y ∈ orderAtLeastLocus I m := hord y hy hyU
      rw [← h2] at h3
      exact h3
    calc derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩)
        = (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ :=
          (derivIdealSheafIterate_ideal k p (m - 1) I ⟨U, hU⟩).symm
      _ ≤ Z.ideal ⟨U, hU⟩ := h1
  have key : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ ^ j := by
    intro j
    induction j with
    | zero => intro hj; exact absurd hj (by omega)
    | succ j ih =>
      intro _ hjm
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        simpa using hbase
      · intro f hf
        have hmem1 : f ∈ derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) :=
          derivIdealIterate_le_of_le k (show m - (j + 1) ≤ m - j by omega) _ hf
        have hfW : f ∈ Z.ideal ⟨U, hU⟩ ^ j := ih hj0 (by omega) hmem1
        have hdf : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Z.ideal ⟨U, hU⟩ ^ j := by
          intro i
          refine ih hj0 (by omega) ?_
          have h4 : (Ds i) f ∈ derivIdeal k (derivIdealIterate k (m - (j + 1)) (I.ideal ⟨U, hU⟩)) :=
            derivation_apply_mem_derivIdeal k _ (Ds i) hf
          rw [← derivIdealIterate_succ] at h4
          exact derivIdealIterate_le_of_le k (show m - (j + 1) + 1 ≤ m - j by omega) _ h4
        have hf' : f ∈ Ideal.span (Set.range xs) ^ j := by rw [hspan]; exact hfW
        have hdf' : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Ideal.span (Set.range xs) ^ j := by
          intro i
          rw [hspan]
          exact hdf i
        have hres := mem_pow_succ_of_deriv_mem_pow k xs Ds hD (hunit j hj0) hf' hdf'
        rw [hspan] at hres
        exact hres
  have hfin := key m hm le_rfl
  rw [Nat.sub_self, derivIdealIterate_zero] at hfin
  exact hfin

theorem le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z I : X.IdealSheafData)
    (m : ℕ)
    (hchart : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S)
    (hord : (Z.support : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_forall_le_pow_basicOpen Z I m ?_
  intro V x hx
  by_cases hxZ : x ∈ Z.support
  · obtain ⟨U, hxU, n, c, S, hS⟩ := hchart x hxZ
    obtain ⟨g, hgU, hxg⟩ := V.2.exists_basicOpen_le (⟨x, hxU⟩ : U) hx
    refine ⟨g, hxg, ?_⟩
    have hWaff : IsAffineOpen (X.basicOpen g) := V.2.basicOpen g
    have hchart' : restrictIdeal Z (X.basicOpen g) = (c.restrict hgU).coordIdeal S :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hgU c Z S hS
    exact ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hWaff (c.restrict hgU) Z S hchart' m I
      (fun y hy _ => hord hy)
  · have hΩopen : IsOpen ((Z.support : Set X)ᶜ) := Z.support.2.isOpen_compl
    have hxΩ : x ∈ (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens) := hxZ
    obtain ⟨g, hgΩ, hxg⟩ :=
      V.2.exists_basicOpen_le (⟨x, hxΩ⟩ : (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens)) hx
    refine ⟨g, hxg, ?_⟩
    have htop : Z.ideal (X.affineBasicOpen g) = ⊤ := by
      refine ideal_eq_top_of_disjoint_support Z (X.affineBasicOpen g) ?_
      intro y hy
      have hy' : y ∈ X.basicOpen g := hy
      exact hgΩ hy'
    rw [htop, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top]
    exact le_top

theorem le_pow_of_hasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z I : X.IdealSheafData)
    (E : List X.IdealSheafData) (hE : HasStrictNormalCrossingsWith p Z E) (m : ℕ)
    (hord : (Z.support : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal p Z I m ?_ hord
  unfold HasStrictNormalCrossingsWith at hE
  intro x hx
  obtain ⟨U, hxU, n, c, _, S, _, _, _, hZ⟩ := hE x hx
  exact ⟨U, hxU, n, c, S, hZ⟩

end FunctorialResolution.EmbeddedResolution
