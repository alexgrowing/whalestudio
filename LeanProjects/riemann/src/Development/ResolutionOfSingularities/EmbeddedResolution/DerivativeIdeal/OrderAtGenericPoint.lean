import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisibility
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem span_eq_top_of_forall_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ x : X, x ∈ U → ∃ t ∈ s, x ∈ X.basicOpen t) :
    Ideal.span s = ⊤ := by
  have hUeq : (⨆ f : s, X.basicOpen (f : Γ(X, U))) = U := by
    refine le_antisymm (iSup_le fun f => Scheme.basicOpen_le (X := X) (f : Γ(X, U)))
      (SetLike.le_def.mpr ?_)
    intro x hx
    obtain ⟨t, hts, hxt⟩ := hcov x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, hts⟩, hxt⟩
  exact (IsAffineOpen.iSup_basicOpen_eq_self_iff hU).mp hUeq

private theorem exists_mul_mem_of_map_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
    (b : Ideal R) (f : R) (hf : g f ∈ Ideal.map g b) :
    ∃ t ∈ M, t * f ∈ b := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have hf' : algebraMap R S f ∈ Ideal.map (algebraMap R S) b := hf
  obtain ⟨⟨y, m⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)).mp hf'
  rw [← map_mul] at he
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp he
  refine ⟨(c : R) * (m : R), M.mul_mem c.2 m.2, ?_⟩
  have h3 : (c : R) * (m : R) * f = (c : R) * (y : R) := by rw [← hc]; ring
  rw [h3]
  exact b.mul_mem_left _ y.2

private theorem isUnit_map_of_mem_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
    (t : R) (ht : t ∈ M) : IsUnit (g t) := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have h1 : IsUnit (algebraMap R S t) := IsLocalization.map_units S (⟨t, ht⟩ : M)
  exact h1

private theorem mem_of_span_mul_mem_eq_top {R : Type*} [CommRing R] (b : Ideal R)
    (f : R) (h : Ideal.span {t : R | t * f ∈ b} = ⊤) : f ∈ b := by
  have hC : ∀ g ∈ Ideal.span {t : R | t * f ∈ b}, g * f ∈ b := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => simp
    | add x y hx hy ihx ihy => simpa [add_mul] using b.add_mem ihx ihy
    | smul a x hx ih => simpa [smul_eq_mul, mul_assoc] using b.mul_mem_left a ih
  have h1 : (1 : R) ∈ Ideal.span {t : R | t * f ∈ b} := by
    rw [h]; exact Submodule.mem_top
  simpa using hC 1 h1

theorem le_iff_forall_stalkIdeal_le {X : Scheme.{u}} (I J : X.IdealSheafData) :
    I ≤ J ↔ ∀ x : X, stalkIdeal I x ≤ stalkIdeal J x := by
  refine ⟨fun h x => stalkIdeal_mono h x, fun h => ?_⟩
  rw [Scheme.IdealSheafData.le_def]
  intro U f hf
  have hU : IsAffineOpen U.1 := U.2
  have hlocal : ∀ (x : X) (hx : x ∈ U.1),
      @IsLocalization ↥Γ(X, U.1) _
        (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) _ ((X.presheaf.germ U.1 x hx).hom.toAlgebra) := by
    intro x hx
    exact IsAffineOpen.isLocalization_stalk hU ⟨x, hx⟩
  have hbasic : ∀ (x : X) (hx : x ∈ U.1) (t : Γ(X, U.1)),
      IsUnit ((X.presheaf.germ U.1 x hx).hom t) → x ∈ X.basicOpen t := by
    intro x hx t ht
    exact (Scheme.mem_basicOpen X t x hx).mpr ht
  have key : ∀ (x : X) (hx : x ∈ U.1),
      ∃ t : Γ(X, U.1), t * f ∈ J.ideal U ∧ x ∈ X.basicOpen t := by
    intro x hx
    have hmemI : (X.presheaf.germ U.1 x hx).hom f ∈ stalkIdeal I x := by
      rw [stalkIdeal_eq_map_germ I x U hx]
      exact Ideal.mem_map_of_mem _ hf
    have hmem : (X.presheaf.germ U.1 x hx).hom f ∈
        Ideal.map (X.presheaf.germ U.1 x hx).hom (J.ideal U) := by
      have hh := h x hmemI
      rwa [stalkIdeal_eq_map_germ J x U hx] at hh
    obtain ⟨t, htM, htf⟩ := exists_mul_mem_of_map_mem_map (X.presheaf.germ U.1 x hx).hom
      (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl (hlocal x hx) (J.ideal U) f hmem
    exact ⟨t, htf, hbasic x hx t (isUnit_map_of_mem_of_isLocalization
      (X.presheaf.germ U.1 x hx).hom _ (hlocal x hx) t htM)⟩
  have hspan : Ideal.span {t : Γ(X, U.1) | t * f ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen hU {t : Γ(X, U.1) | t * f ∈ J.ideal U}
      (fun x hx => ?_)
    obtain ⟨t, htf, hxt⟩ := key x hx
    exact ⟨t, htf, hxt⟩
  exact mem_of_span_mul_mem_eq_top (J.ideal U) f hspan

theorem notMem_support_of_mem_opens_of_restrictIdeal_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData)
    (U : X.Opens) (h : restrictIdeal Z U = ⊤) (x : X) (hx : x ∈ U) : x ∉ Z.support := by
  intro hxZ
  obtain ⟨y, hy⟩ : x ∈ Set.range (⇑U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  have h' : Z.comap U.ι = ⊤ := h
  have h2 := Scheme.IdealSheafData.support_comap Z U.ι
  have h3 : (⇑U.ι) y ∈ Z.support := by
    rw [hy]
    exact hxZ
  have h4 : y ∈ (Z.comap U.ι).support := by
    rw [h2]
    exact h3
  rw [h', Scheme.IdealSheafData.support_top] at h4
  exact h4

def orderAtGenericPoint {X : Scheme.{u}} (I : X.IdealSheafData) {C : Set X}
    (hC : IsIrreducible C) : ℕ∞ :=
  orderAt I hC.genericPoint

theorem orderAtGenericPoint_eq_orderAt {X : Scheme.{u}} (I : X.IdealSheafData) {C : Set X}
    (hC : IsIrreducible C) :
    orderAtGenericPoint I hC = orderAt I hC.genericPoint := rfl

theorem isClosed_of_maximal_irreducible_subset_support {X : Scheme.{u}} (D : X.IdealSheafData)
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C) :
    IsClosed C := by
  have hsupp : IsClosed ((D.support : Set X)) := D.support.2
  have hsub : closure C ⊆ (D.support : Set X) := closure_minimal hCsub hsupp
  have heq : closure C = C := hCmax (closure C) hC.closure subset_closure hsub
  rw [← heq]
  exact isClosed_closure

variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

theorem stalkIdeal_eq_span_germ_coord {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) :
    stalkIdeal D y =
      Ideal.span ({(X.presheaf.germ V y hy).hom (c.coord j)} : Set (X.presheaf.stalk y)) := by
  have h1 : stalkIdeal D y = Ideal.map (X.presheaf.germ V y hy).hom (D.ideal ⟨V, hV⟩) :=
    stalkIdeal_eq_map_germ D y ⟨V, hV⟩ hy
  have h2 : D.ideal ⟨V, hV⟩ = Ideal.span (c.coord '' (({j} : Finset (Fin n)) : Set (Fin n))) :=
    EtaleChart.ideal_eq_span_coord c hV D {j} hD
  rw [h1, h2, Ideal.map_span]
  simp

theorem coord_mem_primeIdealOf_of_mem_support {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  by_contra hcon
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hV.isLocalization_stalk ⟨y, hy⟩
  have hunit : IsUnit ((X.presheaf.germ V y hy).hom (c.coord j)) :=
    IsLocalization.map_units (S := X.presheaf.stalk y)
      (M := (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨c.coord j, hcon⟩
  refine (mem_support_iff_stalkIdeal_ne_top D y).mp hys ?_
  rw [stalkIdeal_eq_span_germ_coord p hV c j D hD y hy]
  exact Ideal.span_singleton_eq_top.mpr hunit

private theorem isUnit_germ_iff_notMem_primeIdealOf {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W) (f : Γ(Y, W)) :
    IsUnit ((Y.presheaf.germ W y hy).hom f) ↔ f ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let _ : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  constructor
  · intro hu hmem
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (↥(Y.presheaf.stalk y))
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal f).mp hu hmem
  · intro hmem
    exact IsLocalization.map_units (S := Y.presheaf.stalk y)
      (M := (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨f, hmem⟩

private theorem primeIdealOf_le_of_specializes {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (a b : Y) (ha : a ∈ W) (hb : b ∈ W) (h : a ⤳ b) :
    (hW.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hW.primeIdealOf ⟨b, hb⟩).asIdeal := by
  intro f hf
  by_contra hcon
  have hb' : b ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f b hb).mpr ((isUnit_germ_iff_notMem_primeIdealOf hW b hb f).mpr hcon)
  have ha' : a ∈ Y.basicOpen f := h.mem_open (Y.basicOpen f).isOpen hb'
  exact ((isUnit_germ_iff_notMem_primeIdealOf hW a ha f).mp
    ((Scheme.mem_basicOpen Y f a ha).mp ha')) hf

private theorem isPrime_span_germ_coord {Y : Scheme.{u}} {K : Type u} [Field K]
    {pr : Y ⟶ Spec (CommRingCat.of K)} {W : Y.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (c : EtaleChart pr W n) (j : Fin n) (y : Y) (hy : y ∈ W)
    (hcoord : c.coord j ∈ (hW.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (Ideal.span ({(Y.presheaf.germ W y hy).hom (c.coord j)} :
      Set (Y.presheaf.stalk y))).IsPrime := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) := c.algebra
  have instEt : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) :=
    c.algebra_etale hW
  let instAlg : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ W y hy).hom.toAlgebra
  have instPrime : ((hW.primeIdealOf ⟨y, hy⟩).asIdeal).IsPrime :=
    (hW.primeIdealOf ⟨y, hy⟩).isPrime
  have instLoc : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal := hW.isLocalization_stalk ⟨y, hy⟩
  have hcoordeq : etaleChartCoord K n (Γ(Y, W)) j = c.coord j := by
    rw [etaleChartCoord_def]
    exact EtaleChart.coordRingHom_X c j
  have h := isPrime_span_singleton_algebraMap_etaleChartCoord K n (Γ(Y, W))
    ((hW.primeIdealOf ⟨y, hy⟩).asIdeal) (Y.presheaf.stalk y) j
    (by rw [hcoordeq]; exact hcoord)
  rw [hcoordeq] at h
  exact h

theorem primeIdealOf_eq_comap_span_germ_coord {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
          Set (X.presheaf.stalk x))) := by
  have hcoordq : c.coord j ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    coord_mem_primeIdealOf_of_mem_support p hV c j D hD η hη hηs
  have hqle : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    primeIdealOf_le_of_specializes hV η x hη hx hspec
  have hsp : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime :=
    isPrime_span_germ_coord hV c j x hx (hqle hcoordq)
  have hPprime : (Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))).IsPrime := inferInstance
  have htP : c.coord j ∈ Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x))) := by
    rw [Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _
  have hmapspan : Ideal.map (X.presheaf.germ V x hx).hom
      (Ideal.span ({c.coord j} : Set Γ(X, V)))
      = Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hloc : @IsLocalization ↥Γ(X, V) _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ↥(X.presheaf.stalk x) _ ((X.presheaf.germ V x hx).hom.toAlgebra) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hPle : Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))
      ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    rw [Ideal.mem_comap, ← hmapspan] at ha
    obtain ⟨s, hs, hsa⟩ := exists_mul_mem_of_map_mem_map (X.presheaf.germ V x hx).hom
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hloc
      (Ideal.span ({c.coord j} : Set Γ(X, V))) a ha
    have hs' : s ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hs
    have hsq : s ∉ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := fun hcon => hs' (hqle hcon)
    have hle : Ideal.span ({c.coord j} : Set Γ(X, V)) ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).mpr hcoordq
    exact ((hV.primeIdealOf ⟨η, hη⟩).isPrime.mem_or_mem (hle hsa)).resolve_left hsq
  exact (hmin _ hPprime htP hPle).symm

theorem stalkIdeal_eq_maximalIdeal_of_minimal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (_hx : x ∈ V) (hη : η ∈ V)
    (_hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) :=
    (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := hV.isLocalization_stalk ⟨η, hη⟩
  have halg : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hsp : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hpeq : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V η hη).hom
        (Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} :
          Set (X.presheaf.stalk η))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD η η hη hη specializes_rfl hηs hmin
  have hne : stalkIdeal D η ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D η).mp hηs
  have hsub : Ideal.comap (X.presheaf.germ V η hη).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ≤
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V η hη).hom a) :=
      IsLocalization.map_units (S := X.presheaf.stalk η)
        (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) ⟨a, hcon⟩
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact ha hunit
  have h1 : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
      (Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η)))
      = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    IsLocalization.map_under (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk η) _
  refine le_antisymm (IsLocalRing.le_maximalIdeal hne) ?_
  rw [hsp, ← h1, Ideal.map_le_iff_le_comap, halg]
  exact le_trans hsub (le_of_eq hpeq)

private theorem mem_span_pow_of_mul_mem_span_pow {A : Type*} [CommRing A] (τ : A)
    (hprime : (Ideal.span ({τ} : Set A)).IsPrime) (hnzd : τ ∈ nonZeroDivisors A) (a : ℕ) :
    ∀ s f : A, s ∉ Ideal.span ({τ} : Set A) →
      s * f ∈ Ideal.span ({τ ^ a} : Set A) → f ∈ Ideal.span ({τ ^ a} : Set A) := by
  induction a with
  | zero =>
      intro s f _ _
      rw [pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
  | succ b ih =>
      intro s f hs hsf
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hsf
      have hsf1 : s * f ∈ Ideal.span ({τ} : Set A) := by
        refine Ideal.mem_span_singleton.mpr ⟨τ ^ b * d, ?_⟩
        rw [hd]
        ring
      have hf1 : f ∈ Ideal.span ({τ} : Set A) := (hprime.mem_or_mem hsf1).resolve_left hs
      obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.mp hf1
      have hcancel : (s * f' - τ ^ b * d) * τ = 0 := by
        have h2 : (s * f' - τ ^ b * d) * τ = s * (τ * f') - τ ^ (b + 1) * d := by ring
        rw [h2, hd, sub_self]
      have hsf' : s * f' = τ ^ b * d :=
        eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp hnzd).2 _ hcancel)
      have hf' : f' ∈ Ideal.span ({τ ^ b} : Set A) :=
        ih s f' hs (Ideal.mem_span_singleton.mpr ⟨d, hsf'⟩)
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hf'
      refine Ideal.mem_span_singleton.mpr ⟨e, ?_⟩
      rw [he]
      ring

theorem stalkIdeal_le_pow_stalkIdeal_of_minimal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal)
    (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I η) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) := (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    hV.isLocalization_stalk ⟨η, hη⟩
  have halgη : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hqcomap : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD x η hx hη hspec hηs hmin
  have hqle : ∀ z : Γ(X, V), (X.presheaf.germ V x hx).hom z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) →
      z ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro z hz
    rw [hqcomap]
    exact hz
  have hnetop : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))) ≠ ⊤ := by
    intro hcon
    have h1 : (hV.primeIdealOf ⟨η, hη⟩).asIdeal = ⊤ := by
      rw [hqcomap, hcon, Ideal.comap_top]
    exact (hV.primeIdealOf ⟨η, hη⟩).isPrime.ne_top h1
  have hqp : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro r hr
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V x hx).hom r) :=
      IsLocalization.map_units (S := X.presheaf.stalk x)
        (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ⟨r, hcon⟩
    have hmemr : (X.presheaf.germ V x hx).hom r ∈
        Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
      rw [hqcomap] at hr
      exact hr
    exact hnetop (Ideal.eq_top_of_isUnit_mem _ hmemr hunit)
  have hdisj : Disjoint ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl : Set (Γ(X, V)))
      ((hV.primeIdealOf ⟨η, hη⟩).asIdeal : Set (Γ(X, V))) := by
    rw [Set.disjoint_left]
    intro r hr hr'
    have hr1 : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hr
    exact hr1 (hqp hr')
  have hqcomap' : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    hqcomap
  have hmapq : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    rw [hqcomap']
    exact IsLocalization.map_under (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x) _
  have hprime : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime := by
    rw [← hmapq]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal (hV.primeIdealOf ⟨η, hη⟩).isPrime hdisj
  have hnzd : (X.presheaf.germ V x hx).hom (c.coord j) ∈
      nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) (coord_mem_nonZeroDivisors hV c j)
  have hDx : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD x hx
  have hDη : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hmaxη : stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x η hx hη hspec hηs hmin
  have hIη : stalkIdeal I η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a :=
    (le_orderAt_iff I η a).mp ha
  have hmapη : IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a =
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmaxη, hDη, Ideal.span_singleton_pow, Ideal.map_span, halgη]
    simp [Set.image_singleton, map_pow]
  rw [hDx, Ideal.span_singleton_pow, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap]
  have hgη : (X.presheaf.germ V η hη).hom g ∈ stalkIdeal I η :=
    germ_mem_stalkIdeal I η ⟨V, hV⟩ hη hg
  have hstep : (X.presheaf.germ V η hη).hom g ∈
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmapη]
    exact hIη hgη
  obtain ⟨w, hw⟩ := (IsLocalization.mem_map_algebraMap_iff
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) (S := X.presheaf.stalk η)).mp hstep
  have hw' : algebraMap (Γ(X, V)) (X.presheaf.stalk η) (g * (w.2 : Γ(X, V))) =
      algebraMap (Γ(X, V)) (X.presheaf.stalk η) ((w.1 : Γ(X, V))) := by
    rw [map_mul]
    exact hw
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
    (S := X.presheaf.stalk η)).mp hw'
  have humem : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∈
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl := Submonoid.mul_mem _ cc.2 w.2.2
  have hug : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g ∈
      Ideal.span ({c.coord j ^ a} : Set (Γ(X, V))) := by
    have heq : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g = (cc : Γ(X, V)) * (w.1 : Γ(X, V)) := by
      rw [← hcc]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ w.1.2
  have hnotin : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∉
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    intro hcon
    exact humem (hqle _ hcon)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hug
  have hA : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) *
      (X.presheaf.germ V x hx).hom g ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j) ^ a} : Set (X.presheaf.stalk x)) := by
    refine Ideal.mem_span_singleton.mpr ⟨(X.presheaf.germ V x hx).hom d, ?_⟩
    rw [← map_mul, hd, map_mul, map_pow]
  exact mem_span_pow_of_mul_mem_span_pow _ hprime hnzd a _ _ hnotin hA

private theorem specializes_of_primeIdealOf_le {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) (a b : Y) (ha : a ∈ V) (hb : b ∈ V)
    (h : (hV.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hV.primeIdealOf ⟨b, hb⟩).asIdeal) : a ⤳ b := by
  rw [specializes_iff_mem_closure, mem_closure_iff]
  intro W hWopen hbW
  have hbW' : b ∈ (⟨W, hWopen⟩ : Y.Opens) := hbW
  obtain ⟨f, hfW, hbf⟩ :=
    hV.exists_basicOpen_le (⟨b, hbW'⟩ : ↥(⟨W, hWopen⟩ : Y.Opens)) hb
  have hfb : f ∉ (hV.primeIdealOf ⟨b, hb⟩).asIdeal :=
    (isUnit_germ_iff_notMem_primeIdealOf hV b hb f).mp ((Scheme.mem_basicOpen Y f b hb).mp hbf)
  have hfa : f ∉ (hV.primeIdealOf ⟨a, ha⟩).asIdeal := fun hcon => hfb (h hcon)
  have haf : a ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f a ha).mpr ((isUnit_germ_iff_notMem_primeIdealOf hV a ha f).mpr hfa)
  exact ⟨a, SetLike.le_def.mp hfW haf, rfl⟩

private theorem exists_mem_primeIdealOf_eq_of_isPrime {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    (P : Ideal Γ(Y, V)) (hP : P.IsPrime) :
    ∃ (ξ : Y) (hξ : ξ ∈ V), (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal = P := by
  have hsub : Set.range hV.fromSpec.base ⊆ (V : Set Y) := hV.range_fromSpec.subset
  have hmem : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) ∈ V :=
    hsub (Set.mem_range_self _)
  refine ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem, ?_⟩
  have h1 : hV.fromSpec.base (hV.primeIdealOf
      ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩) =
      hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) :=
    hV.fromSpec_primeIdealOf ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩
  exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective h1)

theorem exists_etaleChart_genericPoint_mem (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (hη : hC.genericPoint ∈ V) (n : ℕ)
      (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧ hC.genericPoint ⤳ x ∧
        hC.genericPoint ∈ D.support ∧
        ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
          P ≤ (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal →
          P = (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal := by
  have hCclosed : IsClosed C := isClosed_of_maximal_irreducible_subset_support D hC hCsub hCmax
  have hgen0 : closure ({hC.genericPoint} : Set X) = closure C :=
    (QuasiSober.sober hC.closure isClosed_closure).choose_spec
  have hgen : closure ({hC.genericPoint} : Set X) = C := by
    rw [hgen0]
    exact hCclosed.closure_eq
  have hηC : hC.genericPoint ∈ C := by
    have h1 : hC.genericPoint ∈ closure ({hC.genericPoint} : Set X) := subset_closure rfl
    rwa [hgen] at h1
  have hspec : hC.genericPoint ⤳ x := by
    have h1 : x ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hx
    exact specializes_iff_mem_closure.mpr h1
  obtain ⟨U, hxU, n, c, hcase⟩ := hloc x
  have hxsupp : x ∈ D.support := hCsub hx
  have hne : ¬ (restrictIdeal D U = ⊤) := fun htop =>
    notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U htop x hxU hxsupp
  obtain ⟨j, hDU⟩ := hcase.resolve_left hne
  obtain ⟨W, hxW, hW⟩ := Scheme.exists_isAffineOpen_mem x
  obtain ⟨f, hfU, hxf⟩ := hW.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hxW
  have hVaff : IsAffineOpen (X.basicOpen f) := hW.basicOpen f
  have hVU : X.basicOpen f ≤ U := hfU
  have hxV : x ∈ X.basicOpen f := hxf
  have hηV : hC.genericPoint ∈ X.basicOpen f := hspec.mem_open (X.basicOpen f).isOpen hxV
  have hDV : restrictIdeal D (X.basicOpen f) = (c.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hDU
  refine ⟨X.basicOpen f, hVaff, hxV, hηV, n, c.restrict hVU, j, hDV, hspec, hCsub hηC, ?_⟩
  intro P hP hcoord hPle
  obtain ⟨ξ, hξV, hξP⟩ := exists_mem_primeIdealOf_eq_of_isPrime hVaff P hP
  have hξsupp : ξ ∈ D.support := by
    rw [mem_support_iff_stalkIdeal_ne_top,
      stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) j D hDV ξ hξV]
    intro htop
    have hu := Ideal.span_singleton_eq_top.mp htop
    have hnot :=
      (isUnit_germ_iff_notMem_primeIdealOf hVaff ξ hξV ((c.restrict hVU).coord j)).mp hu
    rw [hξP] at hnot
    exact hnot hcoord
  have hξη : ξ ⤳ hC.genericPoint :=
    specializes_of_primeIdealOf_le hVaff ξ hC.genericPoint hξV hηV
      (by rw [hξP]; exact hPle)
  have hclosξ : closure ({ξ} : Set X) ⊆ (D.support : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξsupp) D.support.2
  have hCsubξ : C ⊆ closure ({ξ} : Set X) := by
    have h1 : closure ({hC.genericPoint} : Set X) ⊆ closure ({ξ} : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξη))
        isClosed_closure
    rwa [hgen] at h1
  have hEq : closure ({ξ} : Set X) = C :=
    hCmax _ isIrreducible_singleton.closure hCsubξ hclosξ
  have hξC : ξ ∈ C := by
    have h1 : ξ ∈ closure ({ξ} : Set X) := subset_closure rfl
    rwa [hEq] at h1
  have hηξ : hC.genericPoint ⤳ ξ := by
    have h1 : ξ ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hξC
    exact specializes_iff_mem_closure.mpr h1
  have hle2 : (hVaff.primeIdealOf ⟨hC.genericPoint, hηV⟩).asIdeal ≤ P := by
    rw [← hξP]
    exact primeIdealOf_le_of_specializes hVaff hC.genericPoint ξ hηV hξV hηξ
  exact le_antisymm hPle hle2

theorem stalkIdeal_le_pow_of_le_orderAt_genericPoint (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I hC.genericPoint)
    (x : X) (hx : x ∈ C) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  obtain ⟨V, hV, hxV, hηV, n, c, j, hD, hspec, hηs, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_le_pow_stalkIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hηV hspec
    hηs hmin I a ha

theorem stalkIdeal_genericPoint_eq_maximalIdeal (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C) :
    stalkIdeal D hC.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.genericPoint) := by
  obtain ⟨x, hx⟩ := hC.1
  obtain ⟨V, hV, hxV, hηV, n, c, j, hD, hspec, hηs, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hηV hspec
    hηs hmin

theorem not_stalkIdeal_le_pow_succ_genericPoint (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (I : X.IdealSheafData) (a : ℕ) (ha : orderAt I hC.genericPoint = (a : ℕ∞)) :
    ¬ stalkIdeal I hC.genericPoint ≤ stalkIdeal D hC.genericPoint ^ (a + 1) := by
  intro hcon
  rw [stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC hCsub hCmax] at hcon
  have h : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt I hC.genericPoint :=
    (le_orderAt_iff I hC.genericPoint (a + 1)).mpr hcon
  rw [ha] at h
  have h2 : (a : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self a
  exact absurd h (not_le.mpr h2)

end FunctorialResolution.EmbeddedResolution
