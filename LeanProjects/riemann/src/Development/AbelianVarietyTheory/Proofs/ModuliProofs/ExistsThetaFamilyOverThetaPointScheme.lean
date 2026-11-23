import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VeryDenseClosedPointObjectsOfMinimalPrimesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamGlue
open ShapePull ThetaClosed

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', spMap φ = x := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  exact ⟨φ.hom, rfl⟩

theorem exists_geomPt {S : Scheme.{0}} (p : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (y : Sp K ⟶ S), p ∈ Set.range y :=
  ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p)))) ≫
      S.fromSpecResidueField p, IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩

theorem range_spMap_field {R K : Type} [CommRing R] [Field K] (y : R →+* K) :
    Set.range (spMap y) = {(⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R)} := by
  have h : ∀ p : Sp K, spMap y p = (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R) := fun p => by
    have hp : (show PrimeSpectrum K from p).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    refine PrimeSpectrum.ext ?_
    show Ideal.comap y (show PrimeSpectrum K from p).asIdeal = _
    rw [hp]; rfl
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, h _⟩, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_away_lift {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ X) (x' : Sp R' ⟶ X)
    [IsOpenImmersion x'] (p : PrimeSpectrum R) (hp : x p ∈ Set.range x') :
    ∃ f ∉ p.asIdeal, ∃ z : R' →+* Localization.Away f,
      spMap z ≫ x' = spMap (algebraMap R (Localization.Away f)) ≫ x := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := x ⁻¹' Set.range x') hp (x'.isOpenEmbedding.isOpen_range.preimage x.continuous)
  have h : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ x) ⊆ Set.range x' := by
    rintro _ ⟨q, rfl⟩
    exact hle ((PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le ⟨q, rfl⟩)
  obtain ⟨z, hz⟩ := exists_spMap (IsOpenImmersion.lift x' _ h)
  exact ⟨f, hf, z, by rw [hz, IsOpenImmersion.lift_fac]⟩

theorem span_eq_top_of_coset {g n N' : ℕ} {R : Type} [CommRing R] {v : Ix g (N' ^ 2) → R}
    (h : ∀ q : Ideal R, q.IsPrime → Coset n N' v q) : Ideal.span (Set.range v) = ⊤ := by
  by_contra h'
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
  obtain ⟨c, hc⟩ := h m hm.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

section General

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}

theorem tpull {S S' : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s) (f : S' ⟶ S) (s' : S' ⟶ Sp o) (e : f ≫ s = s') :
    ∃ t' : TObj g k J b s', TMap t' t f := T.exists_thetaLevelAbelianScheme_pullback o g k J b S S' s s' f t e

theorem tcomp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s}
    {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} (h : TMap t' t f)
    (e : f' ≫ f = f'') : TMap t'' t' f' ↔ TMap t'' t f'' :=
  e ▸ (T.thetaLevelPullback_id_comp_cancel o g k J b S S' S'' s s' s'' t t' t'').2 f f' h

theorem shape_pull {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {t : TObj g k J b s}
    {t' : TObj g k J b s'} {f : S' ⟶ S} (h : TMap t' t f) (H : t.Shape Mat κ) : t'.Shape Mat κ := fun j =>
  (shape_prim_pull_and_descend o g k J b Mat κ j j S S' s s' f t t' h).1 H j

theorem retype {S : Scheme.{0}} {s s' : S ⟶ Sp o} (e : s = s') (t : TObj g k J b s) : ∃ t' : TObj g k J b s',
    (∀ (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp o) (u : TObj g k J b s₀) f, TMap t u f → TMap t' u f) ∧
    ∀ (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp o) (u : TObj g k J b s₀) f, TMap u t f → TMap u t' f := by
  subst e
  exact ⟨t, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem shape_of_fibres (h₁ : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] {s : S ⟶ Sp o}
    (t : TObj g k J b s) (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S),
      ∃ t' : TObj g k J b (y ≫ s), TMap t' t y ∧ t'.Shape Mat κ) : t.Shape Mat κ := by
  intro j
  have := t.ab.proper
  refine ⟨fun i => ?_, T.relAmple_of_ample_geometricFibres_abelianScheme h₁ S t.pol _ (DVR.linComb_isLB _ t.isLB _ _) fun K _ _ y => ?_⟩
  · refine Over.OverMorphism.ext (hom_ext_of_geometricPoints_dense (X := S) t.A.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun K _ _ y _ => ?_)
    obtain ⟨t', ⟨φ, h, hL, hpt, hact⟩, hs⟩ := H K y
    have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap y ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
    have p₁ := push_comp h _ (pt i) (hact j)
    have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap y ≫ t.lab a := fun a => push_linComb h _ pt _
    rw [(hs j).1 i, p₂] at p₁
    exact congrArg (fun q => q.left) p₁.symm
  · obtain ⟨t', ⟨φ, h, hL, hpt, hact⟩, hs⟩ := H K y
    have i₁ : LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
        ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) :=
      iso_linComb_pull hL _ _ _ φ fun i => by
        fin_cases i
        exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
    obtain ⟨e, he, he'⟩ := grpPullback_iso (isGrpPullback_pullback t.A y) h
    exact (pol_pull _ _ t'.A ((Over.pullback y).obj t.A) (𝟙 _) e.hom.left _ _ (DVR.linComb_isLB _ t'.isLB _ _)
      (pull_isLB (DVR.linComb_isLB _ t.isLB _ _) _) t'.ab (isGrpPullback_of_iso e)
      (i₁.symm.chartPull (chartPullSame _ _ _ _ e.hom.left fun _ => he'.symm) (Geo.Tor.chartPullPull _ _ _ rfl))).2.1 (hs j).2

theorem shape_of_minimalPrimes (h₁ : Out.Laws) (h₂ : Out.Laws2) {R : Type} [CommRing R] [IsNoetherianRing R]
    [_root_.IsReduced R] {s : Sp R ⟶ Sp o} (t : TObj g k J b s)
    (H : ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (s' : Sp K ⟶ Sp o) (t' : TObj g k J b s'),
      RingHom.ker y = q ∧ TMap t' t (spMap y) ∧ t'.Shape Mat κ) : t.Shape Mat κ := by
  refine shape_of_fibres h₁ t fun K _ _ x => ?_
  obtain ⟨x, rfl⟩ := exists_spMap x
  have := RingHom.ker_isPrime x
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := RingHom.ker x) bot_le
  obtain ⟨K', _, y, s', t', rfl, hm, hs⟩ := H q hq
  have := RingHom.ker_isPrime y
  obtain ⟨tq, htq⟩ := tpull t (spMap (Ideal.Quotient.mk (RingHom.ker y))) _ rfl
  have hq : tq.Shape Mat κ := by
    refine T.thetaLevelShape_of_generic_point h₁ h₂ o g k J b Mat κ _ _ tq K' (spMap (RingHom.kerLift y)) s' t' ?_
      ((tcomp htq ((spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r => RingHom.kerLift_mk y r)))).2 hm) hs
    rw [range_spMap_field, genericPoint_eq_bot_of_affine]
    congr 1
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (RingHom.kerLift_injective y))
  have e : spMap (Ideal.Quotient.lift (RingHom.ker y) x hle) ≫ spMap (Ideal.Quotient.mk (RingHom.ker y)) = spMap x :=
    (spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r => rfl))
  obtain ⟨u, hu⟩ := tpull tq (spMap (Ideal.Quotient.lift (RingHom.ker y) x hle)) (spMap x ≫ s)
    (by rw [← Category.assoc, e])
  exact ⟨u, (tcomp htq e).1 hu, shape_pull hu hq⟩

theorem dense_fromSet {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t₀ : TObj g k J b s) (H : ∀ p : S, ∃ (S' : Scheme.{0}) (x : S' ⟶ S) (t : TObj g k J b (x ≫ s)),
      p ∈ Set.range x ∧ TMap t t₀ x ∧ Dense (fromSet em C t)) : Dense (fromSet em C t₀) := by
  intro p
  obtain ⟨S', x, t, ⟨p, rfl⟩, ht, hd⟩ := H p
  refine closure_mono ?_ (image_closure_subset_closure_image x.continuous ⟨p, hd p, rfl⟩)
  rintro _ ⟨_, ⟨K, _, y, ⟨p, rfl⟩, K₀, _, β, i, j, u₀, tx, tc, a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩
  obtain ⟨tx', c, -⟩ := retype (Category.assoc y x s).symm tx
  exact ⟨K, _, y ≫ x, ⟨p, rfl⟩, K₀, _, β, i, j, u₀, tx', tc, a₁, (Category.assoc _ _ _).trans a₂,
    (tcomp ht rfl).1 (c _ _ _ _ a₃), c _ _ _ _ a₄, a₅, a₆⟩

end General

section Theta

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}

theorem hasTh_iff {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {t : TObj g (N' ^ 2) J b s}
    {t' : TObj g (N' ^ 2) J b s'} {f : S' ⟶ S} (h : TMap t' t f) {R : Type} [CommRing R] {x : Sp R ⟶ S'}
    {x' : Sp R ⟶ S} (e : x ≫ f = x') (v : Ix g (N' ^ 2) → R) : t'.HasTh x v ↔ t.HasTh x' v :=
  e ▸ T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b S s t S' s' t' f R x v h

theorem hasTh_pull (h₂ : Out.Laws2) {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {s : Sp R ⟶ Sp o}
    {s' : Sp R' ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {t' : TObj g (N' ^ 2) J b s'} (h : TMap t' t (spMap φ))
    {v : Ix g (N' ^ 2) → R} (H : t.HasTh (𝟙 _) v) : t'.HasTh (𝟙 _) (fun a => φ (v a)) :=
  (hasTh_iff h ((Category.id_comp _).trans (Category.comp_id _).symm) _).2 (T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ s t R R' φ _ v H)

theorem hasTh_iff_secCoord (h₁ : Out.Laws) (h₂ : Out.Laws2) (ho : Odd N') (h2 : 2 ≤ N') {X : Scheme.{0}} {s : X ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (M : LB X) (hM : M.IsLB) (th : Ix g (N' ^ 2) → M.Sec)
    (H : ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v ∧ t.HasTh x v)
    (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R) : t.HasTh x v ↔ SecCoord M th x v := by
  have sp : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), t.HasTh x v →
      Ideal.span (Set.range v) = ⊤ := fun R _ x v h => span_eq_top_of_coset fun q hq =>
    T.thetaCosetNonvanishing_of_hasTh h₁ h₂ o g N' J b X s t N' R x v q h2 dvd_rfl h hq
  have key : ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ w,
      SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) w ∧
      t.HasTh (spMap (algebraMap R (Localization.Away f)) ≫ x) w := fun p => by
    obtain ⟨R', _, x', v', _, hp, a, c⟩ := H (x p)
    obtain ⟨f, hf, z, e⟩ := exists_away_lift x x' p hp
    exact ⟨f, hf, fun i => z (v' i), e ▸ (Coord.secCoord_bc_scale_unique X M _ th R' x' v' hM a).1 _ z,
      e ▸ T.hasThetaConstants_ring_baseChange h₂ o g N' J b X s t R' _ z x' v' c⟩
  refine ⟨fun h => T.isSectionCoordinateVector_of_locally_on_ring X M _ th R x v hM (sp R x v h) fun p => ?_,
    fun h => hasTh_of_local t ho fun q hq => ?_⟩
  · obtain ⟨f, hf, w, a, c⟩ := key p
    refine ⟨Localization.Away f, inferInstance, algebraMap R _, inferInstance,
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge hf, ?_⟩
    obtain ⟨u, hu⟩ := T.thetaConstants_unique_up_to_unit h₁ h₂ o g N' J b X s t _ _ w _ c
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b X s t R _ (algebraMap R (Localization.Away f)) x v h) (sp _ _ _ c)
    rw [funext hu]
    exact (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM a).2.1 u
  · obtain ⟨f, hf, w, a, c⟩ := key ⟨q, hq⟩
    refine ⟨f, hf, ?_⟩
    obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM a).2.2 _
      ((Coord.secCoord_bc_scale_unique X M _ th R x v hM h).1 _ (algebraMap R (Localization.Away f)))
    rw [funext hu]
    exact hasTh_unit_mul t u c

theorem exists_glued (h₁ : Out.Laws) (h₂ : Out.Laws2) (ho : Odd N') {m : ℕ} (hm : 2 ≤ m) (hm' : m ^ 2 ∣ N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {X : Scheme.{0}} [IsReduced X] [IsLocallyNoetherian X]
    (s : X ⟶ Sp o) (M : LB X) (hM : M.IsLB) (th : Ix g (N' ^ 2) → M.Sec)
    (H : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x → SecCoord M th x v →
      ∃ t : TObj g (N' ^ 2) J b (x ≫ s), Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) v ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (z : R →+* K) (t' : TObj g (N' ^ 2) J b (spMap z ≫ x ≫ s)),
          t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => z (v a)) → TMap t' t (spMap z)) :
    ∃ t : TObj g (N' ^ 2) J b s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧
      (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), t.HasTh x v ↔ SecCoord M th x v) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X) (t' : TObj g (N' ^ 2) J b (x ≫ s)) v,
        t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord M th x v → TMap t' t x := by
  choose R iR x v hx hp hv using (T.sectionCoordinateVector_exists_locally X M _ th hM).2.2
  choose t hd hs ht hu using fun p => H (R p) (x p) (v p) (hx p) (hv p)
  have uniq : ∀ (p : X) (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp (R p)) (s' : Sp K ⟶ Sp o)
      (t' : TObj g (N' ^ 2) J b s') (y : Sp K ⟶ X) w, z ≫ x p = y → s' = y ≫ s → t'.Shape Mat κ → t'.HasTh (𝟙 _) w →
      SecCoord M th y w → TMap t' (t p) z := by
    intro p K _ _ z s' t' y w e e' a c d
    obtain ⟨z, rfl⟩ := exists_spMap z
    subst e
    rw [Category.assoc] at e'
    subst e'
    obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM d).2.2 _
      ((Coord.secCoord_bc_scale_unique X M _ th _ _ _ hM (hv p)).1 _ z)
    refine hu p K z t' a ?_
    rw [funext hu']
    exact hasTh_unit_mul t' u c
  have lift : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (p : X) (z : Sp K ⟶ Sp (R p)), z ≫ x p = y := fun K _ y => by
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have := hx (y (IsLocalRing.closedPoint K))
    refine ⟨y (IsLocalRing.closedPoint K), IsOpenImmersion.lift _ y ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q (IsLocalRing.closedPoint K)]
    exact hp _
  obtain ⟨t₀, h₀⟩ := T.exists_thetaLevelAbelianScheme_glue_affineCover h₁ h₂ o g N' J b m X s X R x t hm hm' ho hx (fun p => ⟨p, hp p⟩) (by
    intro i i' A _ a a' u ha e hu₁
    have := hx i
    have : IsReduced (Sp A) := isReduced_of_isOpenImmersion (a ≫ x i)
    have : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 this
    have e₁ : a' ≫ x i' ≫ s = a ≫ x i ≫ s := by rw [← Category.assoc, ← e, Category.assoc]
    generalize hs' : a ≫ x i ≫ s = s' at u e₁ hu₁
    obtain ⟨β, rfl⟩ := exists_spMap s'
    obtain ⟨u', hu'⟩ := tpull (t i') a' _ e₁
    refine (tcomp hu' (Category.id_comp _)).1
      (T.thetaLevel_iso_unique_of_dense_common_fibres h₁ h₂ o g N' J b m A β u u' hm hm' ho (Dense.mono (fun p _ => ?_) dense_univ)).1
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt p
    obtain ⟨w, hw⟩ := tpull u y _ rfl
    refine ⟨K, _, y, w, hy, hw, (tcomp hu' rfl).2 ?_⟩
    obtain ⟨z, hz⟩ := exists_spMap (y ≫ a)
    have hw' := (tcomp hu₁ hz.symm).1 hw
    exact uniq i' K (y ≫ a') _ w (spMap z ≫ x i) _ (by rw [hz, Category.assoc, Category.assoc, e])
      (by rw [hz, ← hs']; simp only [Category.assoc]) (shape_pull hw' (hs i)) (hasTh_pull h₂ hw' (ht i))
      ((Coord.secCoord_bc_scale_unique X M _ th _ _ _ hM (hv i)).1 _ z))
  refine ⟨t₀, dense_fromSet t₀ fun p => ⟨_, x p, t p, hp p, h₀ p, hd p⟩, shape_of_fibres h₁ t₀ fun K _ _ y => ?_,
    hasTh_iff_secCoord h₁ h₂ ho ?_ t₀ M hM th fun p => ⟨R p, _, x p, v p, hx p, hp p, hv p,
      (hasTh_iff (h₀ p) (Category.id_comp _) _).1 (ht p)⟩, fun K _ _ y t' w a c d => ?_⟩
  · obtain ⟨p, z, e⟩ := lift K y
    obtain ⟨u, hu'⟩ := tpull (t p) z (y ≫ s) (by rw [← Category.assoc, e])
    exact ⟨u, (tcomp (h₀ p) e).1 hu', shape_pull hu' (hs p)⟩
  · exact le_trans (by nlinarith) (Nat.le_of_dvd ho.pos hm')
  · obtain ⟨p, z, e⟩ := lift K y
    exact (tcomp (h₀ p) e).1 (uniq p K z _ t' y w e rfl a c d)

end Theta

end GlobalTheory.FamGlue

namespace GlobalTheory.ZM
open FamGlue ThetaClosed

theorem exists_family_over_MMPre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ Y : MMPre n (n ^ j) (thIdeal em C), ∃ t : TObj g ((n ^ j) ^ 2) J b Y.s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v ↔ SecCoord Y.de Y.th x v) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' t x := by
  intro h₁ h₂ crit g J _ Mat κ n w w' hn ho
  obtain ⟨j₁, H₁⟩ := T.exists_theta_family_from_very_dense_points h₁ h₂ g J Mat κ n hn ho
  obtain ⟨j₂, H₂⟩ := T.veryDense_closedPoint_objects_of_minimalPrimes h₁ h₂ crit g J Mat κ n w w' hn ho
  obtain ⟨j₃, H₃⟩ := T.exists_generic_object_minimalPrime_moduli_chart h₁ h₂ g J Mat κ n w w' hn ho
  refine ⟨max (max j₁ j₂) (max j₃ 2), fun j hj o _ b em C d hb hC Y => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hj
  have : IsDedekindDomain o := hb.1
  have := Y.reduced
  have := Y.flat
  have lft : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, -, e⟩ := Y.qproj
    have := isProper_str o N
    rw [← e]; infer_instance
  have : IsLocallyNoetherian Y.MM := LocallyOfFiniteType.isLocallyNoetherian Y.s
  refine exists_glued h₁ h₂ ho.pow hn.two_le (pow_dvd_pow n hj.2.2) Y.s Y.de Y.isLB Y.th fun R _ x v hx hv => ?_
  have hred : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have a₁ : LocallyOfFiniteType (x ≫ Y.s) := inferInstance
  have a₂ : Flat (x ≫ Y.s) := inferInstance
  generalize hs : x ≫ Y.s = s at a₁ a₂
  obtain ⟨β, rfl⟩ := exists_spMap s
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at a₁
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at a₂
  letI := β.toAlgebra
  have ft : Algebra.FiniteType o R := a₁
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o R
  have gen := H₃ j hj.2.1 o b em C d hb hC Y R β x v hx hs hv
  obtain ⟨t, ht, hu⟩ := H₁ j hj.1.1 o b R β v (H₂ j hj.1.2 o b em C d hb hC R v ft hred a₂ (Y.loc R β x v hs hv)
    fun q hq => by
      obtain ⟨K, _, y, e, tq, tc, c₁, -, -, -, c₂, c₃, c₄⟩ := gen q hq
      exact ⟨K, _, y, tq, c₁, c₂, c₃, c₄⟩)
  have gen' : ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K)
      (t' : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)), RingHom.ker y = q ∧ TMap t' t (spMap y) ∧ t'.Shape Mat κ ∧
        FromC em C t (spMap y) := fun q hq => by
    obtain ⟨K, _, y, e, tq, tc, c₁, c₂, c₃, c₄, c₅, -, c₆⟩ := gen q hq
    let i := algebraMap K (AlgebraicClosure K)
    obtain ⟨t', ht'⟩ := tpull tq (spMap i) (spMap (i.comp y) ≫ spMap β) (by rw [← Category.assoc, spMap_comp'])
    have hm := hu _ (i.comp y) t' (shape_pull ht' c₅) (hasTh_pull h₂ ht' c₆)
    obtain ⟨t₀, -, h₀⟩ := retype (spMap_comp' β y) tq
    refine ⟨_, inferInstance, i.comp y, t', ?_, hm, shape_pull ht' c₅, K, _, y.comp β, i, e, t₀, t', tc, c₂, ?_, hm,
      h₀ _ _ _ _ ht', h₀ _ _ _ _ c₄, c₃⟩
    · rw [← c₁, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot i).1 i.injective]
      rfl
    · rw [spMap_comp', spMap_comp', RingHom.comp_assoc]
  refine ⟨t, fun p => ?_, shape_of_minimalPrimes h₁ h₂ t fun q hq => ?_, ht, hu⟩
  · obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := (show PrimeSpectrum R from p).asIdeal) bot_le
    obtain ⟨K, _, y, t', rfl, -, -, c⟩ := gen' q hq
    refine closure_mono (s := {(⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R)}) ?_
      ((PrimeSpectrum.le_iff_mem_closure _ _).1 hle)
    rintro _ rfl
    exact ⟨K, _, spMap y, (range_spMap_field y).ge rfl, c⟩
  · obtain ⟨K, _, y, t', c₁, c₂, c₃, -⟩ := gen' q hq
    exact ⟨K, _, y, _, t', c₁, c₂, c₃⟩

end GlobalTheory.ZM
