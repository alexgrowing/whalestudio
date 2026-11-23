import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrimeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaCoordinateSchemeDataStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.OpenFamily
open GlobalTheory.ThetaClosed

section General
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}

def cast {s s₁ : S ⟶ Sp o} (t : TObj g k J b s) (h : s = s₁) : TObj g k J b s₁ := h ▸ t

theorem tmap_cast_left {s s₁ : S ⟶ Sp o} (t : TObj g k J b s) (h : s = s₁) {s' : S' ⟶ Sp o} (u : TObj g k J b s')
    (f : S ⟶ S') : TMap (cast t h) u f ↔ TMap t u f := by
  subst h; exact Iff.rfl

theorem tmap_cast_right {s s₁ : S ⟶ Sp o} (t : TObj g k J b s) (h : s = s₁) {s' : S' ⟶ Sp o} (u : TObj g k J b s')
    (f : S' ⟶ S) : TMap u (cast t h) f ↔ TMap u t f := by
  subst h; exact Iff.rfl

theorem shape_cast {s s₁ : S ⟶ Sp o} (t : TObj g k J b s) (h : s = s₁)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) : (cast t h).Shape Mat κ ↔ t.Shape Mat κ := by
  subst h; exact Iff.rfl

theorem hasTh_cast {N' : ℕ} {b : TBase o (N' ^ 2)} {s s₁ : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (h : s = s₁)
    {R : Type} [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) : (cast t h).HasTh x v ↔ t.HasTh x v := by
  subst h; exact Iff.rfl

theorem tmap_comp {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s} {t' : TObj g k J b s'}
    {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (h' : TMap t'' t' f') (h : TMap t' t f) :
    TMap t'' t (f' ≫ f) := TMap.comp h' h

theorem tmap_id {s : S ⟶ Sp o} (t : TObj g k J b s) : TMap t t (𝟙 S) := TMap.refl t

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', x = spMap φ := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [spMap]

theorem fromC_of_tmap {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {K : Type} [Field K] {s' : Sp K ⟶ Sp o}
    {t' : TObj g k J b s'} {s : S ⟶ Sp o} {t : TObj g k J b s} {z : Sp K ⟶ S} (h : FromC em C t' (𝟙 _))
    (hz : TMap t' t z) (e : s' = z ≫ s) : FromC em C t z := by
  obtain ⟨K₀, hK₀, β, i, j, t₀, tx, tc, hj, hs, hx, hx0, hc, hC⟩ := h
  have e' : 𝟙 _ ≫ s' = z ≫ s := by rw [Category.id_comp, e]
  refine ⟨K₀, hK₀, β, i, j, t₀, cast tx e', tc, hj, ?_, ?_, ?_, hc, hC⟩
  · rw [← e', hs]
  · rw [tmap_cast_left]; simpa using TMap.comp hx hz
  · rw [tmap_cast_left]; exact hx0

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (y : R →+* K) (p : Sp R)
    (h : RingHom.ker y = (show PrimeSpectrum R from p).asIdeal) : p ∈ Set.range (spMap y) := by
  refine ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap y ⟨⊥, Ideal.bot_prime⟩).asIdeal = _
  rw [← h, RingHom.ker_eq_comap_bot]
  rfl

theorem exists_minimal_mem {R : Type} [CommRing R] (W : Set (Sp R)) (hW : IsOpen W) {p : Sp R} (hp : p ∈ W) :
    ∃ q ∈ W, (show PrimeSpectrum R from q).asIdeal ∈ minimalPrimes R := by
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal R) ≤ (show PrimeSpectrum R from p).asIdeal from bot_le)
  have hqp : q.IsPrime := hq.1.1
  refine ⟨(⟨q, hqp⟩ : PrimeSpectrum R), ?_, hq⟩
  have hs : (⟨q, hqp⟩ : PrimeSpectrum R) ⤳ (show PrimeSpectrum R from p) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  exact hs.mem_open hW hp

theorem exists_fac_field {R K : Type} [CommRing R] [Field K] (x : Sp R ⟶ S) [IsOpenImmersion x] (z : Sp K ⟶ S)
    (p : Sp K) (hp : z p ∈ Set.range x) : ∃ y : R →+* K, spMap y ≫ x = z := by
  have hsub : Set.range z ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    have hq : q = p := by
      first
      | exact Subsingleton.elim q p
      | exact PrimeSpectrum.ext (by rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from q).asIdeal, Ideal.eq_bot_of_prime (show PrimeSpectrum K from p).asIdeal])
    rw [hq]; exact hp
  obtain ⟨y, hy⟩ := exists_spMap (IsOpenImmersion.lift x z hsub)
  exact ⟨y, by rw [← hy]; exact IsOpenImmersion.lift_fac x z hsub⟩

theorem exists_fac_away {R T : Type} [CommRing R] [CommRing T] (x : Sp R ⟶ S) [IsOpenImmersion x] (z : Sp T ⟶ S)
    (p : Sp T) (hp : z p ∈ Set.range x) : ∃ f ∉ (show PrimeSpectrum T from p).asIdeal,
      ∃ y : R →+* Localization.Away f, spMap y ≫ x = spMap (algebraMap T (Localization.Away f)) ≫ z := by
  have hO : IsOpen (Set.range x) := x.isOpenEmbedding.isOpen_range
  have hO' : IsOpen ((fun q => z q) ⁻¹' Set.range x) := hO.preimage z.continuous
  obtain ⟨V, ⟨f, rfl⟩, hpV, hVsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := T)).exists_subset_of_mem_open
      (a := (show PrimeSpectrum T from p)) hp hO'
  refine ⟨f, hpV, ?_⟩
  have hsub : Set.range (spMap (algebraMap T (Localization.Away f)) ≫ z) ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    have hq : (show PrimeSpectrum T from spMap (algebraMap T (Localization.Away f)) q) ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum T)) := by
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      intro hf
      have h1 : algebraMap T (Localization.Away f) f ∈ (show PrimeSpectrum (Localization.Away f) from q).asIdeal := hf
      exact (show PrimeSpectrum (Localization.Away f) from q).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 (IsLocalization.Away.algebraMap_isUnit f))
    obtain ⟨r, hr⟩ := hVsub hq
    refine ⟨r, ?_⟩
    first
    | simp [hr]
    | (rw [hr]; simp)
    | exact hr
  obtain ⟨y, hy⟩ := exists_spMap (IsOpenImmersion.lift x _ hsub)
  exact ⟨y, by rw [← hy]; exact IsOpenImmersion.lift_fac x _ hsub⟩

theorem isReduced_of_open {R : Type} [CommRing R] [IsReduced S] (x : Sp R ⟶ S) [IsOpenImmersion x] :
    _root_.IsReduced R := by
  haveI : IsReduced (Sp R) := isReduced_of_isOpenImmersion x
  exact (affine_isReduced_iff (CommRingCat.of R)).1 this

theorem isNoetherianRing_of_open {R : Type} [CommRing R] [IsNoetherianRing o] {s : S ⟶ Sp o} (hs : IsQProjOver s)
    (x : Sp R ⟶ S) [IsOpenImmersion x] : IsNoetherianRing R := by
  obtain ⟨N, i, hi, hqc, hcomp⟩ := hs
  haveI : IsImmersion i := hi
  haveI : IsProper (PSpace.str o N) := isProper_str o N
  haveI : LocallyOfFiniteType (PSpace.str o N) := inferInstance
  haveI : LocallyOfFiniteType i := inferInstance
  haveI : IsLocallyNoetherian (Sp o) := inferInstance
  haveI : LocallyOfFiniteType (x ≫ i ≫ PSpace.str o N) := inferInstance
  haveI : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian (x ≫ i ≫ PSpace.str o N)
  first
  | exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 this
  | exact isLocallyNoetherian_Spec.1 this
  | exact (isNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance
  | exact (isNoetherian_Spec (R := CommRingCat.of R)).1 (IsNoetherian.mk)
  | exact (isNoetherian_Spec (R := CommRingCat.of R)).1 { }

end General

section Charts
variable {o : Type} [CommRing o] {g N' n : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
  {C : TObj g (N' ^ 2) J b (spMap em) → Prop}

def IsChart {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} (Y : MMPre n N' I)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ Y.MM)
    (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)) : Prop :=
  IsOpenImmersion x ∧ SecCoord Y.de Y.th x v ∧ t.HasTh (𝟙 _) v ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Sp R) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s')
      (v' : Ix g (N' ^ 2) → K), s' = y ≫ x ≫ Y.s → t'.Shape Mat κ → t'.HasTh (𝟙 _) v' →
      SecCoord Y.de Y.th (y ≫ x) v' → TMap t' t y

def GenericObj (C : TObj g (N' ^ 2) J b (spMap em) → Prop) {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x → SecCoord Y.de Y.th x v →
    ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (y : R →+* K)
      (t : TObj g (N' ^ 2) J b (spMap y ≫ x ≫ Y.s)), RingHom.ker y = q ∧ t.Shape Mat κ ∧
      t.HasTh (𝟙 _) (fun a => y (v a)) ∧ FromC em C t (𝟙 _)

variable {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} {Y : MMPre n N' I}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}

theorem hasTh_of_tmap (h₂ : Out.Laws2) {S : Scheme.{0}} {s : S ⟶ Sp o} {R R' : Type} [CommRing R] [CommRing R']
    {s₁ : Sp R ⟶ Sp o} {t : TObj g (N' ^ 2) J b s₁} {u : TObj g (N' ^ 2) J b s} {x : Sp R ⟶ S} (h : TMap t u x)
    {v : Ix g (N' ^ 2) → R} (hv : t.HasTh (𝟙 _) v) (φ : R →+* R') : u.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  have h1 := GlobalTheory.hasTh_baseChange h₂ _ _ _ _ _ _ _ t _ _ φ (𝟙 _) v hv
  have h2 := (GlobalTheory.hasTh_iff_of_tmap _ _ _ _ _ _ _ u _ _ t x _ _ _ h).1 h1
  simpa using h2

theorem hasTh_pull (h₂ : Out.Laws2) {R R' : Type} [CommRing R] [CommRing R'] {s : Sp R ⟶ Sp o} {s' : Sp R' ⟶ Sp o}
    {t : TObj g (N' ^ 2) J b s} {t' : TObj g (N' ^ 2) J b s'} {φ : R →+* R'} (h : TMap t' t (spMap φ))
    {v : Ix g (N' ^ 2) → R} (hv : t.HasTh (𝟙 _) v) : t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  have h1 := GlobalTheory.hasTh_baseChange h₂ _ _ _ _ _ _ _ t _ _ φ (𝟙 _) v hv
  refine (GlobalTheory.hasTh_iff_of_tmap _ _ _ _ _ _ _ t _ _ t' _ _ _ _ h).2 ?_
  simpa using h1

theorem genericObj_of (h₂ : Out.Laws2) (w w' : J)
    (H : ∀ (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x →
      x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → ∀ q ∈ minimalPrimes R,
      ∃ (K : Type) (_ : Field K) (y : R →+* K) (e : K →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap y ≫ spMap β))
        (tc : TObj g (N' ^ 2) J b (spMap em)), RingHom.ker y = q ∧ e.comp (y.comp β) = em ∧ C tc ∧
        TMap tc t (spMap e) ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => y (v a))) :
    GenericObj C Y Mat κ := by
  unfold GenericObj
  intro R _ x v hx hsc q hq
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Y.s)
  obtain ⟨K, _, y, e, t, tc, hker, he, hC, htc, hsh, -, hth⟩ := H R β x v hx hβ hsc q hq
  have hbase : spMap em = spMap (e.comp y) ≫ x ≫ Y.s := by
    rw [hβ, GlobalTheory.ThetaClosed.spMap_comp', ← he, RingHom.comp_assoc]
  have hbase' : spMap em = 𝟙 _ ≫ (spMap (e.comp y) ≫ x ≫ Y.s) := by
    rw [Category.id_comp]; exact hbase
  have hb1 : spMap y ≫ spMap β = spMap (y.comp β) := GlobalTheory.ThetaClosed.spMap_comp' β y
  refine ⟨ℂ, inferInstance, inferInstance, e.comp y, cast tc hbase, ?_, ?_, ?_, ?_⟩
  · rw [← hker]
    first
    | exact RingHom.ker_comp_of_injective y e.injective
    | (ext a; simp [RingHom.mem_ker])
  · rw [shape_cast]
    exact (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ _ Mat κ w w' _ _ _ _ _ t tc htc).1 hsh
  · rw [hasTh_cast]
    exact hasTh_pull h₂ htc hth
  · refine ⟨K, inferInstance, y.comp β, e, e, cast t hb1, cast tc hbase', tc, he, ?_, ?_, ?_, ?_, hC⟩
    · rw [← hbase', GlobalTheory.ThetaClosed.spMap_comp', he]
    · rw [tmap_cast_left, tmap_cast_right]; exact TMap.refl tc
    · rw [tmap_cast_left, tmap_cast_right]; exact htc
    · rw [tmap_cast_right]; exact htc

theorem secCoord_bc {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R}
    (h : SecCoord Y.de Y.th x v) (φ : R →+* R') : SecCoord Y.de Y.th (spMap φ ≫ x) (fun a => φ (v a)) := Coord.baseChange h φ

theorem secCoord_unit {R : Type} [CommRing R] {x : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R}
    (h : SecCoord Y.de Y.th x v) (u : Rˣ) : SecCoord Y.de Y.th x (fun a => u * v a) := Coord.scale h u

theorem hasTh_of_secCoord {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ Y.MM} {z : Sp R ⟶ S} {v v' : Ix g (N' ^ 2) → R} (h : SecCoord Y.de Y.th x v)
    (h' : SecCoord Y.de Y.th x v') (ht : t.HasTh z v) : t.HasTh z v' := by
  obtain ⟨u, hu⟩ := Coord.unique Y.isLB h h'
  have key := GlobalTheory.ThetaClosed.hasTh_unit_mul (u := u) (H := ht)
  have hv : v' = fun a => (u : R) * v a := funext hu
  rw [hv]; exact key

theorem span_of_secCoord {R : Type} [CommRing R] {x : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R}
    (h : SecCoord Y.de Y.th x v) : Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Y.s)
  have hin := Y.loc R β x v hβ h
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨c, hc⟩ := hin.2 M hM.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem exists_chart [IsNoetherianRing o] (hG : GenericObj C Y Mat κ)
    (hB : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R),
      DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v,
      ∃ (f : R) (t : TObj g (N' ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧
        t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K)
          (t' : TObj g (N' ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))),
          t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) →
          TMap t' t (spMap x))
    (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Y.MM) (t' : TObj g (N' ^ 2) J b (z ≫ Y.s))
    (v' : Ix g (N' ^ 2) → K) (hsh : t'.Shape Mat κ) (hth : t'.HasTh (𝟙 _) v') (hv' : SecCoord Y.de Y.th z v')
    (p : Sp K) : ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
      (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), IsChart Y Mat κ x v t ∧ z p ∈ Set.range x := by
  obtain ⟨R0, _, x0, v0, hx0, hp0, hsc0⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y.MM Y.de _ Y.th Y.isLB).2.2 (z p)
  haveI : IsOpenImmersion x0 := hx0
  haveI : IsReduced Y.MM := Y.reduced
  haveI : _root_.IsReduced R0 := isReduced_of_open x0
  haveI : IsNoetherianRing R0 := isNoetherianRing_of_open Y.qproj x0
  obtain ⟨β, hβ⟩ := exists_spMap (x0 ≫ Y.s)
  obtain ⟨y0, hy0⟩ := exists_fac_field x0 z p hp0
  have hD : DenseP (objPrimes b Mat κ β v0) := by
    intro f hf
    have hmem : f ∈ (⊥ : Ideal R0).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      refine Submodule.mem_sInf.2 (fun q hq => ?_)
      obtain ⟨K, _, _, y, t, hker, hsh, hth, -⟩ := hG R0 x0 v0 hx0 hsc0 q hq
      have hb : spMap y ≫ x0 ≫ Y.s = spMap y ≫ spMap β := by rw [hβ]
      exact hf q ⟨K, inferInstance, inferInstance, y, cast t hb, hker, by rw [shape_cast]; exact hsh,
        by rw [hasTh_cast]; exact hth⟩ hq.1.1
    obtain ⟨n, hn⟩ := hmem
    exact IsReduced.eq_zero f ⟨n, Ideal.mem_bot.1 hn⟩
  have hq0 : RingHom.ker y0 ∈ objPrimes b Mat κ β v0 := by
    have hb : z ≫ Y.s = spMap y0 ≫ spMap β := by rw [← hy0, Category.assoc, hβ]
    have hsc1 : SecCoord Y.de Y.th z (fun a => y0 (v0 a)) := by
      rw [← hy0]; exact secCoord_bc hsc0 y0
    refine ⟨K, inferInstance, inferInstance, y0, cast t' hb, rfl, by rw [shape_cast]; exact hsh, ?_⟩
    rw [hasTh_cast]
    exact hasTh_of_secCoord hv' hsc1 hth
  obtain ⟨f, t, hf, hth0, huniv⟩ := hB R0 β v0 hD _ hq0
  have hbt : spMap ((algebraMap R0 (Localization.Away f)).comp β) =
      (spMap (algebraMap R0 (Localization.Away f)) ≫ x0) ≫ Y.s := by
    rw [Category.assoc, hβ, GlobalTheory.ThetaClosed.spMap_comp']
  haveI : IsOpenImmersion (spMap (algebraMap R0 (Localization.Away f))) := by
    first
    | infer_instance
    | (unfold spMap; infer_instance)
  refine ⟨Localization.Away f, inferInstance, spMap (algebraMap R0 (Localization.Away f)) ≫ x0,
    fun a => algebraMap R0 (Localization.Away f) (v0 a), cast t hbt, ?_, ?_⟩
  · unfold IsChart
    refine ⟨inferInstance, secCoord_bc hsc0 _, by rw [hasTh_cast]; exact hth0, ?_⟩
    intro K' _ _ y s' t'' v'' hs' hsh'' hth'' hsc''
    obtain ⟨y', rfl⟩ := exists_spMap y
    have hb2 : s' = spMap y' ≫ spMap ((algebraMap R0 (Localization.Away f)).comp β) := by rw [hs', ← hbt]
    have hsc2 := secCoord_bc (secCoord_bc hsc0 (algebraMap R0 (Localization.Away f))) y'
    have hth2 : t''.HasTh (𝟙 _) (fun a => y' (algebraMap R0 (Localization.Away f) (v0 a))) :=
      hasTh_of_secCoord hsc'' hsc2 hth''
    have key := huniv K' y' (cast t'' hb2) (by rw [shape_cast]; exact hsh'') (by rw [hasTh_cast]; exact hth2)
    rw [tmap_cast_left] at key
    rw [tmap_cast_right]; exact key
  · have h1 : (spMap y0 p) ∈ Set.range (spMap (algebraMap R0 (Localization.Away f))) := by
      change (show PrimeSpectrum R0 from spMap y0 p) ∈
        Set.range (PrimeSpectrum.comap (algebraMap R0 (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      change f ∉ Ideal.comap y0 (show PrimeSpectrum K from p).asIdeal
      rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from p).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact hf
    obtain ⟨r, hr⟩ := h1
    refine ⟨r, ?_⟩
    rw [← hy0]
    simp [hr]

theorem chart_compat (h₁ : Out.Laws) (h₂ : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (hG : GenericObj C Y Mat κ) {R R' T : Type} [CommRing R] [CommRing R'] [CommRing T]
    {x : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R} {t : TObj g (N' ^ 2) J b (x ≫ Y.s)} (hc : IsChart Y Mat κ x v t)
    {x' : Sp R' ⟶ Y.MM} {v' : Ix g (N' ^ 2) → R'} {t' : TObj g (N' ^ 2) J b (x' ≫ Y.s)} (hc' : IsChart Y Mat κ x' v' t')
    (a : Sp T ⟶ Sp R) (a' : Sp T ⟶ Sp R') {s₁ : Sp T ⟶ Sp o} (u : TObj g (N' ^ 2) J b s₁) (hs : s₁ = a ≫ x ≫ Y.s)
    [IsOpenImmersion a] (e : a ≫ x = a' ≫ x') (hu : TMap u t a) : TMap u t' a' := by
  obtain ⟨φ, rfl⟩ := exists_spMap a
  obtain ⟨β, rfl⟩ := exists_spMap s₁
  haveI : IsOpenImmersion x := hc.1
  haveI : IsReduced Y.MM := Y.reduced
  haveI : _root_.IsReduced R := isReduced_of_open x
  haveI : IsReduced (Sp R) := (affine_isReduced_iff (CommRingCat.of R)).2 inferInstance
  haveI : _root_.IsReduced T := isReduced_of_open (spMap φ)
  obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull _ _ _ _ b _ _ (x' ≫ Y.s) (spMap β) a' t'
    (by rw [hs, ← Category.assoc, ← e, Category.assoc])
  have hvT := secCoord_bc hc.2.1 φ
  have hD : Dense {p : Sp T | ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ Sp T) (w : TObj g (N' ^ 2) J b (z ≫ spMap β)),
      p ∈ Set.range z ∧ TMap w u z ∧ TMap w u' z} := by
    rw [dense_iff_inter_open]
    rintro V hV ⟨p, hp⟩
    obtain ⟨q, hqV, hqmin⟩ := exists_minimal_mem V hV hp
    obtain ⟨K, _, _, y, tK, hker, hsh, hth, -⟩ := hG T (spMap φ ≫ x) _ inferInstance hvT _ hqmin
    have h1 : TMap tK t (spMap y ≫ spMap φ) :=
      hc.2.2.2 K (spMap y ≫ spMap φ) _ tK _ (by simp only [Category.assoc]) hsh hth
        (by simpa only [Category.assoc] using secCoord_bc hvT y)
    have eq2 : (spMap y ≫ a') ≫ x' = spMap y ≫ spMap φ ≫ x := by rw [Category.assoc, e]
    have h2 : TMap tK t' (spMap y ≫ a') :=
      hc'.2.2.2 K (spMap y ≫ a') _ tK _ (by simp only [Category.assoc, reassoc_of% e]) hsh hth
        (by rw [eq2]; exact secCoord_bc hvT y)
    have h3 : TMap tK u (spMap y) := TMap.cancel hu h1
    have h4 : TMap tK u' (spMap y) := TMap.cancel hu' h2
    have hbK : spMap y ≫ (spMap φ ≫ x) ≫ Y.s = spMap y ≫ spMap β := by
      rw [hs]; simp only [Category.assoc]
    obtain ⟨pt, hpt⟩ := mem_range_spMap y q hker
    refine ⟨q, hqV, K, inferInstance, spMap y, cast tK hbK, ⟨pt, hpt⟩, ?_, ?_⟩
    · rw [tmap_cast_left]; exact h3
    · rw [tmap_cast_left]; exact h4
  have hfin := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres h₁ h₂ _ _ _ _ b m T β u u' hm hd ho hD).1
  have := TMap.comp hfin hu'
  rwa [Category.id_comp] at this

end Charts

section Glue
variable {o : Type} [CommRing o] {g N' n : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
  {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
  {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} {Y : MMPre n N' I}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
  {U : Y.MM.Opens} {univ : TObj g (N' ^ 2) J b (U.ι ≫ Y.s)}

def Covered (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (univ : TObj g (N' ^ 2) J b (U.ι ≫ Y.s)) : Prop :=
  ∀ p : U.toScheme, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ U.toScheme) (v : Ix g (N' ^ 2) → R)
    (t : TObj g (N' ^ 2) J b ((x ≫ U.ι) ≫ Y.s)), IsChart Y Mat κ (x ≫ U.ι) v t ∧ p ∈ Set.range x ∧ TMap t univ x

theorem Covered.dense (h : Covered Mat κ univ) (hG : GenericObj C Y Mat κ) : Dense (fromSet em C univ) := by
  rw [dense_iff_inter_open]
  rintro V hV ⟨p, hp⟩
  obtain ⟨R, _, x, v, t, hc, ⟨r, hr⟩, hmap⟩ := h p
  haveI : IsOpenImmersion (x ≫ U.ι) := hc.1
  have hW : IsOpen ((fun q => x q) ⁻¹' V) := hV.preimage x.continuous
  obtain ⟨q, hqW, hqmin⟩ := exists_minimal_mem _ hW (p := r) (show x r ∈ V by rw [hr]; exact hp)
  obtain ⟨K, _, _, y, t'', hker, hsh, hth, hfc⟩ := hG R (x ≫ U.ι) v hc.1 hc.2.1 _ hqmin
  have hsc := secCoord_bc hc.2.1 y
  have htm := hc.2.2.2 K (spMap y) _ t'' (fun a => y (v a)) rfl hsh hth hsc
  have htu := TMap.comp htm hmap
  have hfc2 := fromC_of_tmap hfc htu (by simp only [Category.assoc])
  obtain ⟨pt, hpt⟩ := mem_range_spMap y q hker
  have e3 : (spMap y ≫ x) pt = x q := by
    rw [← hpt]
    first
    | rfl
    | simp
  refine ⟨(spMap y ≫ x) pt, ?_, ⟨K, inferInstance, spMap y ≫ x, ⟨pt, rfl⟩, hfc2⟩⟩
  rw [e3]; exact hqW

theorem Covered.exists_local (h : Covered Mat κ univ) (h₂ : Out.Laws2) {R : Type} [CommRing R]
    (z : Sp R ⟶ U.toScheme) (p : PrimeSpectrum R) : ∃ f ∉ p.asIdeal, ∃ w : Ix g (N' ^ 2) → Localization.Away f,
      univ.HasTh (spMap (algebraMap R (Localization.Away f)) ≫ z) w ∧
      SecCoord Y.de Y.th (spMap (algebraMap R (Localization.Away f)) ≫ z ≫ U.ι) w := by
  obtain ⟨R', _, x, v, t, hc, hp, hmap⟩ := h (z p)
  haveI : IsOpenImmersion (x ≫ U.ι) := hc.1
  haveI : IsOpenImmersion x := IsOpenImmersion.of_comp x U.ι
  obtain ⟨f, hf, y, hy'⟩ := exists_fac_away x z p hp
  refine ⟨f, hf, fun a => y (v a), ?_, ?_⟩
  · rw [← hy']; exact hasTh_of_tmap h₂ hmap hc.2.2.1 y
  · have e2 : spMap (algebraMap R (Localization.Away f)) ≫ z ≫ U.ι = spMap y ≫ x ≫ U.ι := by
      rw [← Category.assoc, ← hy', Category.assoc]
    rw [e2]; exact secCoord_bc hc.2.1 y

theorem Covered.hasTh_iff (h : Covered Mat κ univ) (h₁ : Out.Laws) (h₂ : Out.Laws2) (ho : Odd N') (R : Type)
    [CommRing R] (z : Sp R ⟶ U.toScheme) (v : Ix g (N' ^ 2) → R) :
    univ.HasTh z v ↔ SecCoord Y.de Y.th (z ≫ U.ι) v := by
  constructor
  · intro ht
    have loc : ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal,
        SecCoord Y.de Y.th (spMap (algebraMap R (Localization.Away f)) ≫ z ≫ U.ι)
          (fun a => algebraMap R (Localization.Away f) (v a)) := by
      intro p
      obtain ⟨f, hf, w, hw1, hw2⟩ := h.exists_local h₂ z p
      have hb := GlobalTheory.hasTh_baseChange h₂ _ _ _ _ _ _ _ univ _ _ (algebraMap R (Localization.Away f)) z v ht
      obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit h₁ h₂ _ _ _ _ _ _ _ univ _ _ _ _ hw1 hb (span_of_secCoord hw2)
      refine ⟨f, hf, ?_⟩
      have e : (fun a => algebraMap R (Localization.Away f) (v a)) = fun a => (u : Localization.Away f) * w a :=
        funext hu
      rw [e]; exact secCoord_unit hw2 u
    have hspan : Ideal.span (Set.range v) = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨f, hf, hsc⟩ := loc ⟨M, hM.isPrime⟩
      have h1 := span_of_secCoord hsc
      have h2 : Ideal.map (algebraMap R (Localization.Away f)) M = ⊤ := by
        rw [eq_top_iff, ← h1, Ideal.span_le]
        rintro _ ⟨a, rfl⟩
        exact Ideal.mem_map_of_mem _ (hle (Ideal.subset_span ⟨a, rfl⟩))
      have hdis : Disjoint (Submonoid.powers f : Set R) (M : Set R) := by
        rw [Set.disjoint_left]
        rintro _ ⟨n, rfl⟩ hn
        exact hf (hM.isPrime.mem_of_pow_mem n hn)
      exact (IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) M
        hM.isPrime hdis).ne_top h2
    refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring _ Y.de _ Y.th R (z ≫ U.ι) v Y.isLB hspan (fun p => ?_)
    obtain ⟨f, hf, hsc⟩ := loc p
    refine ⟨Localization.Away f, inferInstance, algebraMap R (Localization.Away f), ?_, ?_, hsc⟩
    · first
      | infer_instance
      | (unfold spMap; infer_instance)
    · change p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact hf
  · intro hs
    refine GlobalTheory.ThetaClosed.hasTh_of_local univ ho (fun q hq => ?_)
    obtain ⟨f, hf, w, hw1, hw2⟩ := h.exists_local h₂ z ⟨q, hq⟩
    exact ⟨f, hf, hasTh_of_secCoord hw2 (secCoord_bc hs _) hw1⟩

theorem Covered.tmap (h : Covered Mat κ univ) (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ U.toScheme)
    {s' : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s') (hs : s' = z ≫ U.ι ≫ Y.s) (v' : Ix g (N' ^ 2) → K)
    (hsh : t'.Shape Mat κ) (hth : t'.HasTh (𝟙 _) v') (hv' : SecCoord Y.de Y.th (z ≫ U.ι) v') : TMap t' univ z := by
  have pt : Sp K := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum K)
  obtain ⟨R, _, x, v, t, hc, hp, hmap⟩ := h (z pt)
  haveI : IsOpenImmersion (x ≫ U.ι) := hc.1
  obtain ⟨r, hr⟩ := hp
  obtain ⟨y, hy⟩ := exists_fac_field (x ≫ U.ι) (z ≫ U.ι) pt ⟨r, by simp [hr]⟩
  have hz : spMap y ≫ x = z := by
    rw [← cancel_mono U.ι]; simpa using hy
  have hv'' : SecCoord Y.de Y.th (spMap y ≫ x ≫ U.ι) v' := by
    rw [← hz] at hv'; simpa using hv'
  have key := hc.2.2.2 K (spMap y) s' t' v' (by rw [hs, ← hz]; simp only [Category.assoc]) hsh hth hv''
  have := TMap.comp key hmap
  rw [hz] at this
  exact this

theorem exists_covered (h₁ : Out.Laws) (h₂ : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (hG : GenericObj C Y Mat κ) : ∃ (U : Y.MM.Opens) (univ : TObj g (N' ^ 2) J b (U.ι ≫ Y.s)), Covered Mat κ univ ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)),
        IsChart Y Mat κ x v t → Set.range x ⊆ U := by
  classical
  let W : Set Y.MM := {p | ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), IsChart Y Mat κ x v t ∧ p ∈ Set.range x}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨R, _, x, v, t, hc, hp⟩
    haveI : IsOpenImmersion x := hc.1
    exact ⟨Set.range x, fun q hq => ⟨R, inferInstance, x, v, t, hc, hq⟩, x.isOpenEmbedding.isOpen_range, hp⟩
  let U : Y.MM.Opens := ⟨W, hW⟩
  have hUι : ∀ q : U.toScheme, U.ι q = q.1 := fun q => by
    first
    | rfl
    | simp
  have hrange : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
      (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), IsChart Y Mat κ x v t → Set.range x ⊆ Set.range U.ι := by
    intro R _ x v t hc q hq
    exact ⟨⟨q, ⟨R, inferInstance, x, v, t, hc, hq⟩⟩, hUι _⟩
  have hmem : ∀ i : U.toScheme, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
      (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), IsChart Y Mat κ x v t ∧ i.1 ∈ Set.range x := fun i => i.2
  choose R hR x v t hc hx using hmem
  letI : ∀ i, CommRing (R i) := hR
  let x' : ∀ i, Sp (R i) ⟶ U.toScheme := fun i => IsOpenImmersion.lift U.ι (x i) (hrange (x i) (v i) (t i) (hc i))
  have hx' : ∀ i, x' i ≫ U.ι = x i := fun i => IsOpenImmersion.lift_fac _ _ _
  haveI : ∀ i, IsOpenImmersion (x' i) := fun i => by
    haveI : IsOpenImmersion (x i) := (hc i).1
    haveI : IsOpenImmersion (x' i ≫ U.ι) := by rw [hx' i]; infer_instance
    exact IsOpenImmersion.of_comp (x' i) U.ι
  have hb : ∀ i, x i ≫ Y.s = x' i ≫ U.ι ≫ Y.s := fun i => by rw [← Category.assoc, hx' i]
  let t' : ∀ i, TObj g (N' ^ 2) J b (x' i ≫ U.ι ≫ Y.s) := fun i => cast (t i) (hb i)
  haveI : IsReduced Y.MM := Y.reduced
  haveI : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have hcov : ∀ p : U.toScheme, p ∈ Set.range (x' p) := by
    intro p
    obtain ⟨r, hr⟩ := hx p
    refine ⟨r, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [hUι p, ← hr, ← hx' p]
    first
    | simp
    | rfl
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_glue_affineCover h₁ h₂ _ _ _ _ b m U.toScheme (U.ι ≫ Y.s) U.toScheme R x' t' hm hd ho
    (fun i => inferInstance) (fun p => ⟨p, hcov p⟩) (fun i i' T _ a a' u ha e hu => by
      haveI := ha
      have e' : a ≫ x i = a' ≫ x i' := by
        rw [← hx' i, ← hx' i', ← Category.assoc, e, Category.assoc]
      have hu' : TMap u (t i) a := (tmap_cast_right (t i) (hb i) u a).1 hu
      have key := chart_compat h₁ h₂ hm hd ho hG (hc i) (hc i') a a' u (by rw [hb i]) e' hu'
      exact (tmap_cast_right (t i') (hb i') u a').2 key)
  refine ⟨U, t₀, fun p => ?_, fun R _ x v t hc => fun q hq => ⟨R, inferInstance, x, v, t, hc, hq⟩⟩
  have hb2 : x p ≫ Y.s = (x' p ≫ U.ι) ≫ Y.s := by rw [hx' p]
  have tr : ∀ (x₂ : Sp (R p) ⟶ Y.MM) (e : x p = x₂), IsChart Y Mat κ x₂ (v p) (cast (t p) (by rw [e])) := by
    rintro _ rfl; exact hc p
  refine ⟨R p, inferInstance, x' p, v p, cast (t p) hb2, tr _ (hx' p).symm, hcov p, ?_⟩
  exact (tmap_cast_left _ _ _ _).2 ((tmap_cast_left (t p) (hb p) _ _).1 (ht₀ p))

end Glue

theorem nonempty_wFam : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (WFam n em C Mat κ) := by
  intro h₁ h₂ g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_generic_object_minimalPrime_moduli_chart h₁ h₂ g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.exists_thetaObject_near_good_prime h₁ h₂ g J Mat κ n hn hodd
  refine ⟨max (max j₁ j₂) 2, fun j hj o _ b em C d har hgood => ?_⟩
  have hj1 : j ≥ j₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j ≥ j₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 2 ≤ j := le_trans (le_max_right _ _) hj
  haveI : IsDedekindDomain o := har.1
  obtain ⟨hrad, hhom, htf⟩ :=
    GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g (n ^ j) J b em C har.2.2
  obtain ⟨Y⟩ := GlobalTheory.T.nonempty_thetaCoordinateSchemeData o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) hrad hhom htf
  have hG : GenericObj C Y Mat κ := genericObj_of h₂ w w' (hj₁ j hj1 o b em C d har hgood Y)
  have hB := hj₂ j hj2 o b
  have ho : Odd (n ^ j) := hodd.pow
  obtain ⟨U, univ, hcov, hsub⟩ := exists_covered h₁ h₂ hn.two_le (pow_dvd_pow n hj3) ho hG
  refine ⟨WFam.mk Y U univ (hcov.dense hG) (fun R _ x v => hcov.hasTh_iff h₁ h₂ ho R x v) ?_⟩
  intro K _ _ x t' v hsh hth hsc
  have pt : Sp K := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum K)
  obtain ⟨R, _, x1, v1, t1, hc, hx1⟩ := exists_chart hG hB K x t' v hsh hth hsc pt
  have hU : x pt ∈ (U : Set Y.MM) := hsub R x1 v1 t1 hc hx1
  have hrange : Set.range x ⊆ Set.range U.ι := by
    rintro _ ⟨q, rfl⟩
    have hq : q = pt := by
      first
      | exact Subsingleton.elim q pt
      | exact PrimeSpectrum.ext (by rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from q).asIdeal, Ideal.eq_bot_of_prime (show PrimeSpectrum K from pt).asIdeal])
    rw [hq]
    first
    | (rw [Scheme.Opens.range_ι]; exact hU)
    | exact ⟨⟨_, hU⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift U.ι x hrange, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  exact hcov.tmap K _ t' (by rw [← Category.assoc, IsOpenImmersion.lift_fac]) v hsh hth
    (by rw [IsOpenImmersion.lift_fac]; exact hsc)

end GlobalTheory.ZM.OpenFamily
end
