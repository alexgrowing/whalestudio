import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_prime_le_under_eq_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hle : p ≤ Ideal.under R Q) :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ Ideal.under R P = p := by
  rcases eq_or_lt_of_le hle with h | h
  · exact ⟨Q, le_rfl, ‹Q.IsPrime›, h.symm⟩
  · obtain ⟨P, hPQ, hP, hlo⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) Q h
    exact ⟨P, hPQ, hP, hlo.over.symm⟩

private theorem exists_ltSeries_le_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (n : ℕ) :
    ∀ (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∀ (Q : Ideal S), Q.IsPrime → p.last.asIdeal ≤ Ideal.under R Q →
        ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧ q.last.asIdeal ≤ Q ∧
          Ideal.under R q.last.asIdeal = p.last.asIdeal := by
  induction n with
  | zero =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      exact ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, hPQ, hunder⟩
  | succ n ih =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      have hlen : p.length ≠ 0 := by omega
      have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hlen
      have hltI : p.eraseLast.last.asIdeal < p.last.asIdeal :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt
      have hlen' : p.eraseLast.length = n := by
        have := RelSeries.eraseLast_length p
        omega
      have hle' : p.eraseLast.last.asIdeal ≤ Ideal.under R P := by
        rw [hunder]
        exact le_of_lt hltI
      obtain ⟨q, hq1, hq2, hq3⟩ := ih p.eraseLast hlen' P hP hle'
      have hne : q.last.asIdeal ≠ P := by
        intro h
        rw [h, hunder] at hq3
        exact (ne_of_lt hltI) hq3.symm
      have hrel : q.last < (⟨P, hP⟩ : PrimeSpectrum S) :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (lt_of_le_of_ne hq2 hne)
      refine ⟨q.snoc ⟨P, hP⟩ hrel, ?_, ?_, ?_⟩
      · rw [RelSeries.snoc_length, hq1]
      · rw [RelSeries.last_snoc]; exact hPQ
      · rw [RelSeries.last_snoc]; exact hunder

private theorem ringKrullDim_le_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.HasGoingDown R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  have key : ∀ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞) ≤ ringKrullDim S := by
    intro p
    have hmax : p.last.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.last.isPrime.ne_top
    have hp : p.last.asIdeal ≤ Ideal.under R (IsLocalRing.maximalIdeal S) := by
      intro x hx
      exact map_nonunit (algebraMap R S) x (hmax hx)
    obtain ⟨q, hq1, -, -⟩ :=
      exists_ltSeries_le_of_hasGoingDown R S p.length p rfl (IsLocalRing.maximalIdeal S)
        inferInstance hp
    calc (p.length : WithBot ℕ∞) = (q.length : WithBot ℕ∞) := by rw [hq1]
      _ ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim q
  exact iSup_le key

private theorem spanFinrank_map_le (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] (I : Ideal R) :
    (Ideal.map (algebraMap R S) I).spanFinrank ≤ I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ := Submodule.exists_span_set_card_eq_spanRank I
  have hIfg : Submodule.FG (I : Submodule R R) := IsNoetherian.noetherian I
  have hrank : I.spanRank = (I.spanFinrank : Cardinal) :=
    Submodule.FG.spanRank_eq_spanFinrank hIfg
  have hslt : Cardinal.mk s < Cardinal.aleph0 := by
    rw [hcard, hrank]
    exact Cardinal.natCast_lt_aleph0
  have hspan' : Ideal.span s = I := hspan
  have hmapspan : Ideal.map (algebraMap R S) I = Ideal.span ((algebraMap R S) '' s) := by
    rw [← hspan', Ideal.map_span]
  have h1 : (Ideal.map (algebraMap R S) I).spanRank ≤ Cardinal.mk ((algebraMap R S) '' s) := by
    rw [hmapspan]
    exact Submodule.spanRank_span_le_card _
  have h2 := Cardinal.mk_image_le_lift (f := (algebraMap R S : R → S)) (s := s)
  have hliftlt : Cardinal.lift.{_, _} (Cardinal.mk s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hslt
  have h4 : Cardinal.mk ((algebraMap R S) '' s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mp (lt_of_le_of_lt h2 hliftlt)
  have h3 : Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) ≤
      Cardinal.toNat (Cardinal.mk s) := by
    have := Cardinal.toNat_le_toNat h2 hliftlt
    rwa [Cardinal.toNat_lift, Cardinal.toNat_lift] at this
  calc (Ideal.map (algebraMap R S) I).spanFinrank
      = Cardinal.toNat (Ideal.map (algebraMap R S) I).spanRank :=
        Submodule.spanFinrank.eq_def _
    _ ≤ Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) := Cardinal.toNat_le_toNat h1 h4
    _ ≤ Cardinal.toNat (Cardinal.mk s) := h3
    _ = I.spanFinrank := by rw [hcard, ← Submodule.spanFinrank.eq_def]

private theorem ringKrullDim_le_of_map_maximalIdeal (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    (hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :
    ringKrullDim S ≤ ringKrullDim R := by
  have : IsNoetherianRing R := inferInstance
  have hne : IsLocalRing.maximalIdeal S ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hh : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ hne
  have hfr : (IsLocalRing.maximalIdeal S).spanFinrank ≤
      (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le R S _
  have hR := (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := R))
  rw [← hR, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
  have h : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal R).spanFinrank : ℕ∞) :=
    le_trans hh (Nat.cast_le.mpr hfr)
  exact_mod_cast h

theorem ringKrullDim_eq_of_flat_formallyUnramified (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have : Algebra.HasGoingDown R S := inferInstance
  have h1 : ringKrullDim R ≤ ringKrullDim S := ringKrullDim_le_of_hasGoingDown R S
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  exact le_antisymm (ringKrullDim_le_of_map_maximalIdeal R S hmax) h1

theorem isRegularLocalRing_of_flat_formallyUnramified (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    _root_.IsRegularLocalRing S := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have hdim : ringKrullDim S = ringKrullDim R := ringKrullDim_eq_of_flat_formallyUnramified R S
  have hR : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  have h4 : (IsLocalRing.maximalIdeal S).spanFinrank
      ≤ (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le R S _
  have hh : (IsLocalRing.maximalIdeal S).height
      ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hle1 : ringKrullDim S ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
    exact_mod_cast hh
  refine (isRegularLocalRing_iff S).mpr (le_antisymm ?_ hle1)
  rw [hdim, ← hR]
  exact_mod_cast h4

private theorem isRegularLocalRing_stalk_of_iso_spec {X : Scheme.{u}} (R : Type u) [CommRing R]
    (hreg : ∀ (p : Ideal R) (hp : p.IsPrime),
      _root_.IsRegularLocalRing (@Localization.AtPrime R _ p hp))
    (e : X ≅ Spec (CommRingCat.of R)) (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  let y : PrimeSpectrum R := e.hom.base x
  have hp : y.asIdeal.IsPrime := y.isPrime
  have h1 : _root_.IsRegularLocalRing (@Localization.AtPrime R _ y.asIdeal hp) :=
    hreg y.asIdeal hp
  have h2 : IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have e2 : Localization.AtPrime y.asIdeal ≃+* ((Spec.structureSheaf R).presheaf.stalk y) :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
      ((Spec.structureSheaf R).presheaf.stalk y)).toRingEquiv
  have h3 : _root_.IsRegularLocalRing ((Spec.structureSheaf R).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv e2
  have h4 : IsIso (e.hom.stalkMap x) := inferInstance
  have e3 : ((Spec.structureSheaf R).presheaf.stalk y) ≃+* (X.presheaf.stalk x) :=
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e3

theorem isRegularLocalRing_stalk_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n]
    (x : AffineSpace n (Spec (CommRingCat.of k))) :
    _root_.IsRegularLocalRing ((AffineSpace n (Spec (CommRingCat.of k))).presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_iso_spec (MvPolynomial n k)
    (fun p hp => by have := hp; infer_instance)
    (AffineSpace.SpecIso n (CommRingCat.of k)) x

private theorem isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y)
    (hZ : _root_.IsRegularLocalRing (Z.presheaf.stalk (f.base y)))
    (hflat : (f.stalkMap y).hom.Flat)
    (heft : (f.stalkMap y).hom.EssFiniteType)
    (hfu : (f.stalkMap y).hom.FormallyUnramified) :
    _root_.IsRegularLocalRing (Y.presheaf.stalk y) := by
  have := hZ
  let _ : Algebra (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hflat
  have : Algebra.EssFiniteType (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := heft
  have : Algebra.FormallyUnramified (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  have : IsNoetherianRing (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.isNoetherianRing
      (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
  exact isRegularLocalRing_of_flat_formallyUnramified
    (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)

private theorem isRegularLocalRing_stalk_of_opens {X : Scheme.{u}} (U : X.Opens) (y : U)
    (h : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk y)) :
    _root_.IsRegularLocalRing (X.presheaf.stalk y.1) := by
  have := h
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv

theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, m, hxU, -, ⟨c⟩⟩ := exists_etaleChart p x
  have := c.isEtale
  have hreg : _root_.IsRegularLocalRing
      ((affineSpaceFin k m).presheaf.stalk (c.map.base (⟨x, hxU⟩ : U))) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) _
  have h2 : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified c.map (⟨x, hxU⟩ : U) hreg
      (AlgebraicGeometry.Flat.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.LocallyOfFiniteType.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.FormallyUnramified.stalkMap c.map (⟨x, hxU⟩ : U))
  exact isRegularLocalRing_stalk_of_opens U (⟨x, hxU⟩ : U) h2

theorem isDomain_stalk_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have : _root_.IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth p x
  exact IsRegularLocalRing.isDomain _

theorem smooth_isRegularLocalRing_stalk {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  have := hp
  exact isRegularLocalRing_stalk_of_smooth p x

theorem smooth_isDomain_stalk {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have := hp
  exact isDomain_stalk_of_smooth p x

theorem isReduced_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth p x
    infer_instance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

theorem smooth_isReduced {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) :
    IsReduced X := by
  have := hp
  exact isReduced_of_smooth p

private noncomputable def pointOfIsoSpec {Y : Scheme.{u}} (R : CommRingCat.{u}) (e : Y ≅ Spec R) (y : Y) :
    PrimeSpectrum ↥R :=
  e.hom.base y

private theorem eq_closure_of_mem_irreducibleComponents {α : Type*} [TopologicalSpace α]
    {V : Set α} (hVopen : IsOpen V) (hVirr : IsIrreducible V) {T : Set α}
    (hT : T ∈ irreducibleComponents α) {x : α} (hxV : x ∈ V) (hxT : x ∈ T) : T = closure V := by
  have hsub : T ⊆ closure V := by
    intro y hy
    rw [mem_closure_iff]
    intro o ho hyo
    obtain ⟨z, -, hzo, hzV⟩ := hT.1.2 o V ho hVopen ⟨y, hy, hyo⟩ ⟨x, hxT, hxV⟩
    exact ⟨z, hzo, hzV⟩
  exact le_antisymm hsub (hT.2 hVirr.closure hsub)

private theorem exists_isOpen_isIrreducible_of_unique_irreducibleComponent {α : Type*} [TopologicalSpace α]
    (hfin : (irreducibleComponents α).Finite) {T₀ : Set α} (hT₀ : IsIrreducible T₀) {z : α}
    (_hz : z ∈ T₀) (huniq : ∀ T ∈ irreducibleComponents α, z ∈ T → T = T₀) :
    ∃ W : Set α, IsOpen W ∧ IsIrreducible W ∧ z ∈ W := by
  have hSfin : Set.Finite {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T} :=
    Set.Finite.subset hfin (fun T hT => hT.1)
  have hScl : IsClosed (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T}) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hSfin
      (fun T hT => isClosed_of_mem_irreducibleComponents _ hT.1)
  have hzW : z ∈ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ := by
    intro hcon
    obtain ⟨T, hTS, hzT⟩ := hcon
    exact hTS.2 hzT
  have hWT : (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ ⊆ T₀ := by
    intro y hy
    have hc : irreducibleComponent y ∈ irreducibleComponents α :=
      irreducibleComponent_mem_irreducibleComponents y
    have hzc : z ∈ irreducibleComponent y := by
      by_contra hcon
      exact hy ⟨irreducibleComponent y, ⟨hc, hcon⟩, mem_irreducibleComponent⟩
    rw [← huniq _ hc hzc]
    exact mem_irreducibleComponent
  refine ⟨_, hScl.isOpen_compl, ⟨⟨z, hzW⟩, ?_⟩, hzW⟩
  intro u v hu hv hu' hv'
  obtain ⟨a, haW, hau⟩ := hu'
  obtain ⟨b, hbW, hbv⟩ := hv'
  obtain ⟨c, -, ⟨hcu, hcW⟩, hcv, -⟩ :=
    hT₀.2 (u ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (v ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (hu.inter hScl.isOpen_compl) (hv.inter hScl.isOpen_compl)
      ⟨a, hWT haW, hau, haW⟩ ⟨b, hWT hbW, hbv, hbW⟩
  exact ⟨c, hcW, hcu, hcv⟩

private theorem exists_isOpen_isIrreducible_of_unique_minimal_prime_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] (P : PrimeSpectrum A) (K : Ideal A) (hK : K.IsPrime)
    (hmin : ∀ q : Ideal A, q.IsPrime → q ≤ P.asIdeal → K ≤ q) :
    ∃ W : Set (PrimeSpectrum A), IsOpen W ∧ IsIrreducible W ∧ P ∈ W := by
  have hT₀irr : IsIrreducible (PrimeSpectrum.zeroLocus (K : Set A)) := by
    rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime,
      PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hK.radical]
    exact hK
  have hPT₀ : P ∈ PrimeSpectrum.zeroLocus (K : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => hmin P.asIdeal P.isPrime le_rfl ha
  have hcomp : ∀ T ∈ irreducibleComponents (PrimeSpectrum A), P ∈ T →
      T = PrimeSpectrum.zeroLocus (K : Set A) := by
    intro T hT hPmem
    have hTcl : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
    have hq : (PrimeSpectrum.vanishingIdeal T).IsPrime :=
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hT.1
    have hTeq : PrimeSpectrum.zeroLocus ((PrimeSpectrum.vanishingIdeal T : Ideal A) : Set A)
        = T := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hTcl.closure_eq]
    have hqP : PrimeSpectrum.vanishingIdeal T ≤ P.asIdeal := fun a ha =>
      (PrimeSpectrum.mem_vanishingIdeal T a).mp ha P hPmem
    have hKq : K ≤ PrimeSpectrum.vanishingIdeal T := hmin _ hq hqP
    have hTsub : T ⊆ PrimeSpectrum.zeroLocus (K : Set A) := by
      rw [← hTeq]
      exact PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.mpr hKq)
    exact le_antisymm hTsub (hT.2 hT₀irr hTsub)
  have hfin : (irreducibleComponents (PrimeSpectrum A)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact exists_isOpen_isIrreducible_of_unique_irreducibleComponent hfin hT₀irr hPT₀ hcomp

private theorem finiteType_appTop_of_isAffineOpen_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.FiniteType (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))
        = V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : AlgebraicGeometry.LocallyOfFiniteType
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2

private theorem isNoetherianRing_sections_of_isAffineOpen_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) : IsNoetherianRing ↥Γ(V.toScheme, ⊤) := by
  have hft := finiteType_appTop_of_isAffineOpen_of_smooth p V hV
  let _ : Algebra ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) :=
    (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop (V.ι ≫ p))).toAlgebra
  have : Algebra.FiniteType ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) := hft
  have : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact Algebra.FiniteType.isNoetherianRing ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤)

private theorem isDomain_localization_of_iso_spec {Y : Scheme.{u}} (R : CommRingCat.{u})
    (e : Y ≅ Spec R) (y : Y) (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) := by
  have := hdom
  have hp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have h2 : IsLocalization.AtPrime
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))
      (pointOfIsoSpec R e y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ↥R (pointOfIsoSpec R e y)
  have e2 : Localization.AtPrime (pointOfIsoSpec R e y).asIdeal ≃+*
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) :=
    (IsLocalization.algEquiv (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))).toRingEquiv
  have h4 : IsIso (e.hom.stalkMap y) := inferInstance
  have e3 : ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) ≃+*
      ↥(Y.presheaf.stalk y) :=
    (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
  exact (e2.trans e3).toMulEquiv.isDomain _

private theorem exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk {Y : Scheme.{u}} (R : CommRingCat.{u})
    [IsNoetherianRing ↥R] (e : Y ≅ Spec R) (y : Y)
    (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    ∃ V : Set Y, IsOpen V ∧ IsIrreducible V ∧ y ∈ V := by
  have hPp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have hdomL : IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) :=
    isDomain_localization_of_iso_spec R e y hdom
  have hbot : (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).IsPrime :=
    Ideal.isPrime_bot
  have hKp : (Ideal.comap
      (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
      (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hmin : ∀ q : Ideal ↥R, q.IsPrime → q ≤ (pointOfIsoSpec R e y).asIdeal →
      Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)) ≤ q := by
    intro q hq hqP a ha
    have h0 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a = 0 := by
      simpa [Ideal.mem_comap, Submodule.mem_bot] using ha
    have h1 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a
        = algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) 0 := by
      rw [h0, map_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).mp h1
    rw [mul_zero] at hc
    have hmem : (c : ↥R) * a ∈ q := by
      rw [hc]
      exact q.zero_mem
    rcases hq.mem_or_mem hmem with h | h
    · exact absurd (hqP h) c.2
    · exact h
  obtain ⟨W, hWopen, hWirr, hPW⟩ :=
    exists_isOpen_isIrreducible_of_unique_minimal_prime_le (pointOfIsoSpec R e y)
      (Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))) hKp hmin
  refine ⟨(Scheme.homeoOfIso e).symm '' W,
    (Scheme.homeoOfIso e).symm.isOpenMap W hWopen,
    hWirr.image _ (Scheme.homeoOfIso e).symm.continuous.continuousOn,
    ⟨pointOfIsoSpec R e y, hPW, (Scheme.homeoOfIso e).symm_apply_apply y⟩⟩

private theorem exists_isOpen_isIrreducible_mem_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨U, hxU, hU'⟩ := Scheme.exists_isAffineOpen_mem x
  have : IsAffine U.toScheme := hU'
  have hnoeth : IsNoetherianRing ↥Γ(U.toScheme, ⊤) := isNoetherianRing_sections_of_isAffineOpen_of_smooth p U hU'
  have hdomX : IsDomain ↥(X.presheaf.stalk x) := isDomain_stalk_of_smooth p x
  have hdomU : IsDomain ↥(U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    (U.stalkIso (⟨x, hxU⟩ : U)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨V, hVopen, hVirr, hyV⟩ :=
    exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk Γ(U.toScheme, ⊤) U.toScheme.isoSpec
      (⟨x, hxU⟩ : U) hdomU
  have hoe := U.ι.isOpenEmbedding
  exact ⟨U.ι.base '' V, hoe.isOpenMap V hVopen,
    hVirr.image _ hoe.continuous.continuousOn, ⟨(⟨x, hxU⟩ : U), hyV, rfl⟩⟩

theorem isClopen_irreducibleComponent_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p)
    {T : Set ↥X} (hT : T ∈ irreducibleComponents ↥X) : IsClopen T := by
  have := hp
  have hclosed : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
  have hopen : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzT
    obtain ⟨W, hWopen, hWirr, hzW⟩ := exists_isOpen_isIrreducible_mem_of_smooth p z
    refine ⟨W, ?_, hWopen, hzW⟩
    rw [eq_closure_of_mem_irreducibleComponents hWopen hWirr hT hzW hzT]
    exact subset_closure
  exact ⟨hclosed, hopen⟩

end FunctorialResolution.EmbeddedResolution
