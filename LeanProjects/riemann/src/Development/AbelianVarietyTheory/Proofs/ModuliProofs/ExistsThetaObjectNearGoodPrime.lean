import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdditionMorphismThetaFamilyNearGoodPrimeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrimeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocLoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChartPullCompOfPullPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsFam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingDataStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpFamOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivNearGoodPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayFlatProjRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NearCOfPolFamOfKTriv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolFamOfGrpFam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolFamBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOpensSmoothOfRelativeDimensionOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricallyConnectedAwayOfFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

section
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R : Type} [CommRing R] {β : o →+* R} {v : Ix g (N' ^ 2) → R}

theorem nearC_of_den_loc (h2 : Out.Laws2) {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀)
    (H : ∀ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ →
      NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁) : NearC b Mat κ β v q₀ := by
  obtain ⟨q₁, hq₁, rfl⟩ := h.loc hf
  exact GlobalTheory.ZM.NearBuild.nearC_of_loc h2 o g N' J b Mat κ R β v f q₁ (isPrime_of_mem hq₁.2) (H q₁ hq₁)

theorem span_map {R' I : Type} [CommRing R'] (ρ : R →+* R') {w : I → R} (h : Ideal.span (Set.range w) = ⊤) :
    Ideal.span (Set.range fun a => ρ (w a)) = ⊤ := by
  have := congrArg (Ideal.map ρ) h
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem span_of_unit {R' I : Type} [CommRing R'] {w : I → R'} (a : I) (h : IsUnit (w a)) :
    Ideal.span (Set.range w) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) h

theorem isUnit_loc {f a : R} (h : a ∣ f) : IsUnit (loc f a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit f)
end

section
variable (h1 : Out.Laws) (h2 : Out.Laws2) {g : ℕ} {J : Type} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
  {κ n j : ℕ} (hn : n.Prime) (hodd : Odd n) (hj : 2 ≤ j) {o : Type} [CommRing o] {b : TBase o ((n ^ j) ^ 2)}
include h1 h2 hn hodd hj

theorem nearC_of_grpFam {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {A : Over (Sp R)} [GrpObj A] {M : LB A.left} {act : J → (A ⟶ A)}
    {Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hA : GrpFam b Mat κ β v (n ^ 2) A M act Q) : NearC b Mat κ β v q₀ := by
  obtain ⟨L, hL⟩ := GlobalTheory.ZM.NearBuild.exists_polFam_of_grpFam h1 h2 o g _ J b Mat κ R β v (n ^ 2) A M act Q (pow_ne_zero _ hn.ne_zero) hodd.pow
    (pow_dvd_pow n hj) h.1 hA
  obtain ⟨f, hf, hK⟩ := GlobalTheory.ZM.NearBuild.kTriv_near_good_prime o g _ J b Mat κ R β v A L act Q q₀ h.2 hL
  obtain ⟨act', Q', hL'⟩ := GlobalTheory.ZM.NearBuild.polFam_baseChange o g _ J b Mat κ R β v A L act Q _ (loc f) hL
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ =>
    GlobalTheory.ZM.NearBuild.nearC_of_polFam_of_kTriv h1 h2 g n j J hn hodd hj o b Mat κ _ _ _ _ _ act' Q' q₁ hq₁ (span_map _ hv) hL' hK

theorem nearC_of_smooth [Finite J]
    (hadd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu)
    (hend : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc)
    (hs : SmoothOfRelativeDimension g Z.hom) : NearC b Mat κ β v q₀ := by
  classical
  have := Fintype.ofFinite J
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  have hs' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hq := isPrime_of_mem h.2
  obtain ⟨f₁, hf₁, hmu⟩ := hadd R β v Z M th sc q₀ h hZ hs'
  choose f₂ hf₂ hF using fun i => hend R β v Z M th sc q₀ i h hZ hs'
  obtain ⟨f₃, hf₃, hc⟩ : ∃ f, f ∉ q₀ ∧ GeometricallyConnected (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ConnSpread.exists_geometricallyConnected_away_of_fibre R _ Z.hom K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).1 hs' ?_
    have := t.ab.geomConnected
    refine MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) this
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  let f := f₁ * f₃ * ∏ i, f₂ i
  have hf : f ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact (hq.mem_or_mem hh).elim hf₁ hf₃
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact hf₂ i hi
  let Z' : Over (Sp (Localization.Away f)) := Over.mk (pullback.snd Z.hom (spMap (loc f)))
  have hpb : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom (spMap (loc f)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨mu, hmu⟩ := hmu _ (loc f) (isUnit_loc ((dvd_mul_right f₁ f₃).mul_right _)) Z' _ hpb
  choose F hF using fun i => hF i _ (loc f)
    (isUnit_loc ((Finset.dvd_prod_of_mem f₂ (Finset.mem_univ i)).mul_left _)) Z' _ hpb
  obtain ⟨th', sc', hZ', hfib⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f) Z' _ hpb hZ
  have hs₁ : SmoothOfRelativeDimension g Z'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb hs
  have hc₁ : GeometricallyConnected Z'.hom := by
    have hu : IsUnit (loc f f₃) := isUnit_loc ((dvd_mul_left f₃ f₁).mul_right _)
    have e : spMap (loc f) = spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃) := by
      rw [← spMap_comp, IsLocalization.Away.lift_comp]
    have hpb' : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom
        (spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃)) := by
      rw [← e]; exact hpb
    have hp₃ := IsPullback.of_hasPullback Z.hom (spMap (loc f₃))
    have := IsPullback.of_right (h₁₁ := hp₃.lift _ _ (hpb'.w.trans (Category.assoc _ _ _).symm))
      (by rw [IsPullback.lift_fst]; exact hpb') (hp₃.lift_snd _ _ _) hp₃
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) this hc
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨_, hG⟩ := GlobalTheory.ZM.NearBuild.grpFam_of_dense_fibres h1 h2 o g _ J b Mat κ _ _ _ _ Z' _ th' sc' mu F (pow_ne_zero _ hn.ne_zero) hq₁.1 hZ' hs₁ hc₁
    (fun K _ _ x s t φ ht hφ => hmu K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
    (fun i K _ _ x s t φ ht hφ => hF i K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
  exact nearC_of_grpFam h1 h2 hn hodd hj hq₁ (span_map _ hv) hG

omit h1 hodd hj in

theorem nearC_of_fam
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → SmoothOfRelativeDimension g Z.hom →
      NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, hs⟩ : ∃ f, f ∉ q₀ ∧ SmoothOfRelativeDimension g (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ProperFlatNearFibre.exists_away_smoothOfRelativeDimension R _ Z.hom g K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).2.1 hZ.2.1 ?_
    refine (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) t.dim
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  obtain ⟨th', sc', hZ', -⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f)
    (Over.mk (pullback.snd Z.hom (spMap (loc f)))) _ (IsPullback.of_hasPullback _ _) hZ
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ => H hq₁ (span_map _ hv) hZ' hs

omit h1 hodd hj in

theorem nearC_of_unimodular
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R} {Hh : Type} [Finite Hh]
    {hh : Hh → Ix g ((n ^ j) ^ 2)} {Q : Polynomial ℚ} {d : ℕ} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hp : ∀ c, Ideal.span (Set.range (p c)) = ⊤)
    (hD : FibData b Mat κ β v (n ^ 2) p hh Q d) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, Z, M, th, hrep, hfl, hfib⟩ := GlobalTheory.ZM.NearCut.exists_away_flat_projRep R _ Hh (fun c => p (hh c)) Q d _ h.1 (fun q hq => by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨σ, I, -, -, -, hc, -⟩ := hD K x s t ht
    exact ⟨K, inferInstance, x, I, rfl, hc⟩) q₀ h.2
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨sc, hZ⟩ := GlobalTheory.ZM.FamOf.exists_sections_fam o g _ J b Mat κ _ _ _ _ _ Hh hh Q d Z M th hq₁.1 (hD.comp (loc f))
    (fun c => span_map _ (hp c)) hrep hfl hfib
  exact H hq₁ (span_map _ hv) hZ
end

theorem exists_tObj_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  classical
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, H₁⟩ := GlobalTheory.T.exists_goodThetaObjectEmbeddingData h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₂, H₂⟩ := GlobalTheory.T.exists_addition_morphism_thetaFamily_near_goodPrime h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₃, H₃⟩ := GlobalTheory.T.exists_endomorphisms_extend_near_good_prime h1 h2 g J Mat κ n hn hodd
  refine ⟨j₁ + j₂ + j₃ + 2, fun j hj o _ b R _ _ _ β v hd q₀ hq₀ => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  suffices H : NearC b Mat κ β v q₀ by
    obtain ⟨f, hf, t, ht, H⟩ := H
    exact ⟨f, t, hf, ht, fun K _ _ x t' k₁ k₂ => H K x _ t' ⟨rfl, k₁, k₂⟩⟩
  obtain ⟨p, Hh, _, hh, Q, d, hD⟩ := H₁ j (by omega) o b R β v
  have hq := isPrime_of_mem hq₀
  obtain ⟨⟨a₀, ha₀⟩, hp⟩ : (∃ a, v a ∉ q₀) ∧ ∀ c, ∃ a, p c a ∉ q₀ := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq₀
    constructor
    · obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh h1 h2 o g _ J b _ s t n K _ _ ⊥ hn.two_le (dvd_pow_self n (by omega)) ht.2.2
        Ideal.isPrime_bot 0
      exact ⟨_, hc⟩
    · intro c
      obtain ⟨σ, I, -, hrep, -, -, hc⟩ := hD K x s t ht
      have := (hrep.2.1 K (RingHom.id K) _ _ (by
        rw [← Over.comp_left, lift_fst]
        exact (Spec.map_id _).symm) (hc c)).1
      by_contra hne
      push Not at hne
      refine (Ideal.isPrime_bot (α := K)).ne_top (eq_top_iff.2 (this ▸ Ideal.span_le.2 ?_))
      rintro _ ⟨a, rfl⟩
      exact hne a
  choose a ha using hp
  have hf : v a₀ * ∏ c, p c (a c) ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact ha₀ hh
    · obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact ha c hc
  refine nearC_of_den_loc h2 ⟨hd, hq₀⟩ hf fun q₁ hq₁ => ?_
  refine nearC_of_unimodular h2 hn (nearC_of_fam h2 hn (nearC_of_smooth h1 h2 hn hodd (by omega)
    (H₂ j (by omega) o b) (H₃ j (by omega) o b))) hq₁
    (span_of_unit a₀ (isUnit_loc (dvd_mul_right _ _))) (fun c => span_of_unit (a c) (isUnit_loc
      ((Finset.dvd_prod_of_mem (fun c => p c (a c)) (Finset.mem_univ c)).mul_left _))) (hD.comp _)

end GlobalTheory.ZM.NearBuild
end
