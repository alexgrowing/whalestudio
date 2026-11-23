import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieGlue

section General

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isPullback_dualMap (f : R →+* R') :
    IsPullback (spMap (Chart.dualMapR f)) (epsR R').hom (epsR R).hom (spMap f) := by
  have w : (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have dec : ∀ {A : Type} [CommRing A] (x : DualNumber A),
      x = algebraMap A (DualNumber A) x.fst + algebraMap A (DualNumber A) x.snd * DualNumber.eps := fun x => by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have he : Chart.dualMapR f DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine isPullback_SpecMap_of_isPushout (CommRingCat.ofHom (algebraMap R (DualNumber R))) (CommRingCat.ofHom f)
    (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ?_
  refine ⟨⟨congrArg CommRingCat.ofHom w⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)⟩⟩
  · letI := s.inr.hom.toAlgebra
    exact CommRingCat.ofHom (DualNumber.lift (R := R') (A := R') ⟨(Algebra.ofId R' s.pt, s.inl.hom DualNumber.eps),
      by rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ => Commute.all _ _⟩).toRingHom
  · have hs : ∀ x, s.inl.hom (algebraMap R (DualNumber R) x) = s.inr.hom (f x) := fun x =>
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.condition) x
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    conv_rhs => rw [dec x, map_add, map_mul, hs, hs]
    simp [DualNumber.lift_apply_apply, Chart.dualMapR]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp
    rfl
  · have e₁ : m.hom DualNumber.eps = s.inl.hom DualNumber.eps := by
      rw [← h₁, ← he]; rfl
    have e₂ : ∀ x, m.hom (algebraMap R' (DualNumber R') x) = s.inr.hom x := fun x => by rw [← h₂]; rfl
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    conv_lhs => rw [dec x, map_add, map_mul, e₁, e₂, e₂]
    simp [DualNumber.lift_apply_apply]
    rfl

theorem exists_glue (f : R →+* R') (hf : Function.Injective f) {A : Over (Sp R)} [IsSeparated A.hom] {I : Type}
    (r : I → R) (hr : Ideal.span (Set.range r) = ⊤) (g : ∀ i, Localization.Away (r i) →+* R')
    (hg : ∀ i, (g i).comp (algebraMap R _) = f) (w : Sp (DualNumber R') ⟶ A.left)
    (t : ∀ i, Sp (DualNumber (Localization.Away (r i))) ⟶ A.left)
    (ht : ∀ i, t i ≫ A.hom = (epsR _).hom ≫ spMap (algebraMap R (Localization.Away (r i))))
    (hw : ∀ i, spMap (Chart.dualMapR (g i)) ≫ t i = w) :
    ∃ u : epsR R ⟶ A, spMap (Chart.dualMapR f) ≫ u.left = w := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have : Flat (epsR R).hom := by
    have : Module.Free R (DualNumber R) := inferInstanceAs (Module.Free R (R × R))
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))))
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  obtain ⟨u, hu, e⟩ := DedekindExt.exists_of_locally (f := w) (epsR R).hom A.hom (isPullback_dualMap f) fun x => by
    have : ∃ i, r i ∉ ((epsR R).hom x : PrimeSpectrum R).asIdeal := by
      by_contra! hc
      exact ((epsR R).hom x : PrimeSpectrum R).isPrime.ne_top
        (top_le_iff.1 (hr ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hc i)))
    obtain ⟨i, hi⟩ := this
    have hp := isPullback_dualMap (algebraMap R (Localization.Away (r i)))
    have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away (r i)))) := inferInstance
    have hopen : IsOpenImmersion (spMap (Chart.dualMapR (algebraMap R (Localization.Away (r i))))) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip ho
    refine ⟨_, _, hopen, t i, ?_, (ht i).trans hp.w.symm, fun T a a' h => ?_⟩
    · have : ((epsR R).hom x : PrimeSpectrum R) ∈
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r i)))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)]
        exact hi
      obtain ⟨y, hy⟩ := this
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hp x y hy.symm
      exact ⟨z, hz⟩
    · rw [← hg i, ← EllComp.dualMapR_comp (algebraMap R _) (g i), ← Category.assoc, cancel_mono] at h
      rw [h, Category.assoc, hw]
  exact ⟨Over.homMk u hu, e⟩

theorem isTangent_of_isVecOver {f : R →+* R'} (hf : Function.Injective f) {A : Over (Sp R)} {A' : Over (Sp R')}
    [GrpObj A] [GrpObj A'] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ)
    {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} (h : IsVecOver f φ v v') (hv : IsTangent v') : IsTangent v := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  refine ExtUnique.hom_ext_of_dominant A.hom ?_ (spMap f) ?_
  · rw [Category.assoc, Over.w v, Over.w η[A]]
    refine (spMap_comp_spMap _ _).trans ?_
    refine Eq.trans ?_ (Spec.map_id (CommRingCat.of R))
    congr 1
  · have e := PolBaseChange.eSec_comm hφ
    unfold eSec at e
    rw [← e, ← hv, Category.assoc, h, ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end General

section Local

variable {R K : Type} [CommRing R] [Field K] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A]
  [IsCommMonObj A] {g : R →+* K} {ψ : A.left ⟶ G.left} {n : ℕ} {e : Fin n → (epsR R ⟶ G)} {v : Fin n → (epsR K ⟶ A)}

theorem exists_matrix (hψ : IsGrpPullback A G (spMap g) ψ) (hs : Smooth G.hom) (he : IsLieBasis e) (hv : IsLieBasis v) :
    ∃ M : Matrix (Fin n) (Fin n) K, M.det ≠ 0 ∧ ∀ j, ∃ w, IsVecOver g ψ (e j) w ∧ IsLieComb (M j) v w := by
  obtain ⟨e', he', h⟩ := exists_isLieBasis_baseChange R K g G A ψ hψ hs n e he
  choose M hM using fun j => (hv.2 _ (he'.1 j)).exists
  exact ⟨M, (((LieComb.lieComb_algebra K A n v hv.1).2.2.2.2 M e' hv hM).1 he').ne_zero, fun j => ⟨e' j, h j, hM j⟩⟩

omit [IsCommMonObj G] in

theorem isVecOver_iff (hψ : IsGrpPullback A G (spMap g) ψ) (hv : IsLieBasis v) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ j, ∃ w, IsVecOver g ψ (e j) w ∧ IsLieComb (M j) v w) {a : Fin n → R} {t : epsR R ⟶ G}
    (ht : IsLieComb a e t) (w : epsR K ⟶ A) : IsVecOver g ψ t w ↔ IsLieComb (∑ j, g (a j) • M j) v w := by
  choose e' h₁ h₂ using hM
  have alg := LieComb.lieComb_algebra K A n v hv.1
  refine (lieComb_baseChange R K g G A ψ hψ n e t a e' w h₁ ht).trans ⟨fun h => alg.2.2.1 n M e' _ w h₂ h, fun h => ?_⟩
  obtain ⟨w', hw', -⟩ := (LieComb.lieComb_algebra K A n e' fun j => alg.2.1 _ _ (h₂ j)).1 fun j => g (a j)
  rwa [(alg.1 _).unique h (alg.2.2.1 n M e' _ w' h₂ hw')]

end Local

theorem exists_comb_iff {R K : Type} [CommRing R] [Field K] [Algebra R K] (r : R) (g : Localization.Away r →+* K)
    (hg : g.comp (algebraMap R _) = algebraMap R K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    (∃ a : Fin n → Localization.Away r, c = ∑ j, g (a j) • M j) ↔
      ∃ (k : ℕ) (a : Fin n → R), r ^ k • c = ∑ j, a j • M j := by
  have hg' : ∀ x, g (algebraMap R _ x) = algebraMap R K x := fun x => RingHom.congr_fun hg x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨_, k, rfl⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers r) a
    choose b hb using h
    refine ⟨k, b, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K (b j), ← hg', hb, ← algebraMap_smul K (r ^ k), smul_smul, ← hg', ← map_mul]
    congr 2
    exact (Algebra.smul_def _ _).symm
  · rintro ⟨k, a, h⟩
    refine ⟨fun j => IsLocalization.Away.invSelf r ^ k * algebraMap R _ (a j), ?_⟩
    have h1 : g (IsLocalization.Away.invSelf r) ^ k * algebraMap R K (r ^ k) = 1 := by
      rw [map_pow, ← mul_pow, ← hg', ← map_mul, _root_.mul_comm, IsLocalization.Away.mul_invSelf, map_one, one_pow]
    rw [← one_smul K c, ← h1, mul_smul, algebraMap_smul, h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hg', mul_smul, algebraMap_smul]

theorem exists_finite_cover {R : Type} [CommRing R] (Q : R → Prop)
    (h : ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, Q r) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ i, r i ≠ 0 ∧ Q (r i) := by
  have h1 : Ideal.span {r | r ≠ 0 ∧ Q r} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hQ⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span ⟨fun e => hr (e ▸ m.zero_mem), hQ⟩))
  obtain ⟨s, hs, h2⟩ := (Ideal.span_eq_top_iff_finite _).1 h1
  refine ⟨s.card, fun i => s.equivFin.symm i, ?_, fun i => hs (s.equivFin.symm i).2⟩
  rw [← h2]
  congr 1
  ext x
  exact ⟨by rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2, fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩

theorem exists_lift {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {f : R →+* R₁} {g : R₁ →+* R₂}
    {h : R →+* R₂} (e : g.comp f = h) {G : Over (Sp R)} {G₁ : Over (Sp R₁)} {G₂ : Over (Sp R₂)} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {φ : G₁.left ⟶ G.left} {χ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G (spMap f) φ)
    (h₂ : IsGrpPullback G₂ G (spMap h) χ) : ∃ ψ, ψ ≫ φ = χ ∧ IsGrpPullback G₂ G₁ (spMap g) ψ := by
  have n' : IsGrpPullback G₂ G (spMap g ≫ spMap f) χ := h₂.congr (by rw [spMap_comp_spMap, e]) rfl
  have w : χ ≫ G.hom = (G₂.hom ≫ spMap g) ≫ spMap f := n'.1.w.trans (Category.assoc _ _ _).symm
  have e' : h₁.1.lift _ _ w ≫ φ = χ := h₁.1.lift_fst _ _ w
  exact ⟨_, e', h₁.cancel (n'.congr rfl e'.symm) (h₁.1.lift_snd _ _ w)⟩

theorem exists_cover_lieLat : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), ∃ (n : ℕ) (r : Fin n → 𝓞 K) (M : Fin n → Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧ (∀ c, c ∈ F.lieLat ↔ ∀ i, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j) ∧
  ∀ i (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left), IsUnit (algebraMap (𝓞 K) R (r i)) → IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → ∃ e : Fin F.P₀.g → (epsR R ⟶ G), IsLieBasis e ∧ ∀ j, ∃ w, IsVecOver (algebraMap R K) ψ (e j) w ∧ IsLieComb (M i j) F.v w := by
  intro K _ _ P F
  have := P.isAb.comm
  have := P.isAb.proper
  have := P.isAb.smooth
  have := F.P₀.isAb.comm
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  obtain ⟨n, r, hr, hQ⟩ := exists_finite_cover _
    (LieLoc.lie_locally_free (𝓞 K) P.A F.P₀.g (F.fib.1 ▸ P.smoothDim))
  choose hr0 e he using hQ
  have hu : ∀ i, IsUnit (algebraMap (𝓞 K) K (r i)) := fun i => ((map_ne_zero_iff _ hinj).2 (hr0 i)).isUnit
  let g : ∀ i, Localization.Away (r i) →+* K := fun i => IsLocalization.Away.lift (r i) (hu i)
  have hg : ∀ i, (g i).comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K := fun i => IsLocalization.Away.lift_comp _ _
  have hφ := fun i => isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))
  have hcomm := fun i => PolPull.isCommMonObj_of_isGrpPullback (hφ i)
  have hsm := fun i => MorphismProperty.of_isPullback (P := @Smooth) (hφ i).1 P.isAb.smooth
  choose ψ hψφ hψ using fun i => exists_lift (hg i) (hφ i) F.fib.2.1
  choose M hdet hM using fun i => exists_matrix (hψ i) (hsm i) (he i) F.basis
  have alg := LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  refine ⟨n, r, M, hr, fun i => ⟨hr0 i, hdet i⟩, fun c => ?_, ?_⟩
  · simp only [← fun i => exists_comb_iff (r i) (g i) (hg i) (M i) c]
    constructor
    · intro hc i
      induction hc using Submodule.span_induction with
      | mem c hc =>
        obtain ⟨u, hu, w, hw, hc⟩ := hc
        obtain ⟨t, ht, -⟩ := existsUnique_isVecOver (f := algebraMap (𝓞 K) (Localization.Away (r i)))
          (A' := (Over.pullback (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))).obj P.A) (hφ i).1 u
        obtain ⟨a, ha, -⟩ := (he i).2 t (ht.isTangent (hφ i) hu)
        have h := EllComp.isVecOver_cancel (hφ i).1 (hψ i).1 ht (by rw [hg, hψφ]; exact hw)
        exact ⟨a, (F.basis.2 w (alg.2.1 _ _ hc)).unique hc ((isVecOver_iff (hψ i) F.basis (hM i) ha w).1 h)⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
      | smul s x _ hx =>
        obtain ⟨a, rfl⟩ := hx
        refine ⟨fun j => algebraMap (𝓞 K) _ s * a j, ?_⟩
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_smul, ← RingHom.comp_apply, hg, algebraMap_smul]
    · intro hc
      choose a ha using hc
      obtain ⟨w, hw, -⟩ := alg.1 c
      choose t ht using fun i => ((LieComb.lieComb_algebra _ _ _ (e i) (he i).1).1 (a i)).exists
      have hwt : ∀ i, IsVecOver (g i) (ψ i) (t i) w := fun i =>
        (isVecOver_iff (hψ i) F.basis (hM i) (ht i) w).2 (ha i ▸ hw)
      obtain ⟨u, hu⟩ := exists_glue _ hinj r hr g hg (w.left ≫ F.φ) (fun i => (t i).left ≫ pullback.fst _ _)
        (fun i => by rw [Category.assoc, (hφ i).1.w, ← Category.assoc, Over.w])
        (fun i => by rw [← Category.assoc, ← hwt i, Category.assoc, hψφ])
      exact Submodule.subset_span
        ⟨u, isTangent_of_isVecOver hinj F.fib.2.1 hu.symm (alg.2.1 _ _ hw), w, hu.symm, hw⟩
  · intro i R _ _ _ _ G _ φ ψ' hri h₁ h₂ h₃
    let l : Localization.Away (r i) →+* R := IsLocalization.Away.lift (r i) hri
    have hl : l.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) R := IsLocalization.Away.lift_comp _ _
    have hgl : (algebraMap R K).comp l = g i := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (r i)) ?_
      rw [RingHom.comp_assoc, hl, hg, ← IsScalarTower.algebraMap_eq]
    obtain ⟨χ, hχφ, hχ⟩ := exists_lift hl (hφ i) h₁
    have := PolPull.isCommMonObj_of_isGrpPullback h₁
    obtain ⟨e', he', hee⟩ := exists_isLieBasis_baseChange _ R l _ G χ hχ (hsm i) _ (e i) (he i)
    have hψχ : ψ' ≫ χ = ψ i := by
      refine (hφ i).1.hom_ext ?_ ?_
      · rw [Category.assoc, hχφ, h₃, hψφ]
      · rw [Category.assoc, hχ.1.w, ← Category.assoc, h₂.1.w, Category.assoc, spMap_comp_spMap, hgl, (hψ i).1.w]
    refine ⟨e', he', fun j => ?_⟩
    obtain ⟨w, hw, hw'⟩ := hM i j
    exact ⟨w, EllComp.isVecOver_cancel hχ.1 h₂.1 (hee j) (by rw [hgl, hψχ]; exact hw), hw'⟩

end GlobalTheory.CM.LieGlue
end
