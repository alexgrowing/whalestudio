import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra

noncomputable section Cover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.LieGlue GlobalTheory.CM.LieLoc GlobalTheory.LieHt

namespace UpperTheory.FibFin

private theorem cover_strong : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), ∃ (n : ℕ) (r : Fin n → 𝓞 K) (M : Fin n → Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧ (∀ c, c ∈ F.lieLat ↔ ∀ i, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j) ∧
  ∀ i (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ F.G.left) (ψ : F.P₀.A.left ⟶ G.left), IsUnit (algebraMap (𝓞 K) R (r i)) → IsGrpPullback G F.G (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → ∃ e : Fin F.P₀.g → (epsR R ⟶ G), IsLieBasis e ∧ ∀ j, ∃ w, IsVecOver (algebraMap R K) ψ (e j) w ∧ IsLieComb (M i j) F.v w := by
  intro K _ _ F
  have := F.semi.comm
  have := F.semi.separated
  have := F.P₀.isAb.comm
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  obtain ⟨n, r, hr, hQ⟩ := exists_finite_cover _
    (GlobalTheory.LieLoc.lie_locally_free (𝓞 K) F.G F.P₀.g F.smoothDim_model)
  choose hr0 e he using hQ
  have hu : ∀ i, IsUnit (algebraMap (𝓞 K) K (r i)) := fun i => ((map_ne_zero_iff _ hinj).2 (hr0 i)).isUnit
  let g : ∀ i, Localization.Away (r i) →+* K := fun i => IsLocalization.Away.lift (r i) (hu i)
  have hg : ∀ i, (g i).comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K := fun i => IsLocalization.Away.lift_comp _ _
  have hφ := fun i => isGrpPullback_pullback F.G (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))
  have hcomm := fun i => PolPull.isCommMonObj_of_isGrpPullback (hφ i)
  have hsm := fun i => MorphismProperty.of_isPullback (P := @Smooth) (hφ i).1 F.semi.smooth
  choose ψ hψφ hψ using fun i => exists_lift (hg i) (hφ i) F.fib
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
          (A' := (Over.pullback (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))).obj F.G) (hφ i).1 u
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
        ⟨u, isTangent_of_isVecOver hinj F.fib hu.symm (alg.2.1 _ _ hw), w, hu.symm, hw⟩
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

private theorem lieLat_loc : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ F.G.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G F.G (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  intro K _ _ F R _ _ _ _ N _ G _ φ ψ e e₀ M hφ hψ hF he hM
  have := F.P₀.isAb.comm
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨n, r, M', -, hr, hL, hb⟩ := cover_strong K F
    have key : ∀ j, ∃ s ∈ N, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), (r j ^ k * s) • M i = ∑ l, a l • M' j l := by
      intro j
      let R' := Localization.Away (algebraMap (𝓞 K) R (r j))
      have hu : IsUnit (algebraMap R K (algebraMap (𝓞 K) R (r j))) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact IsUnit.mk0 _ (by simpa using (hr j).1)
      let g : R' →+* K := IsLocalization.Away.lift (algebraMap (𝓞 K) R (r j)) hu
      have hg : g.comp (algebraMap R R') = algebraMap R K := IsLocalization.Away.lift_comp _ hu
      have hg' : ∀ x, g (algebraMap R R' (algebraMap (𝓞 K) R x)) = algebraMap (𝓞 K) K x := fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R K, ← hg]; rfl
      let _ : Algebra R' K := g.toAlgebra
      have : IsScalarTower (𝓞 K) R' K := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact (hg' x).symm
      have h' := isGrpPullback_pullback G (spMap (algebraMap R R'))
      have n' : IsGrpPullback F.P₀.A G (spMap g ≫ spMap (algebraMap R R')) ψ :=
        hψ.congr (by rw [spMap_comp_spMap, hg]) rfl
      have w : ψ ≫ G.hom = (F.P₀.A.hom ≫ spMap g) ≫ spMap (algebraMap R R') :=
        n'.1.w.trans (Category.assoc _ _ _).symm
      have e₁ := h'.1.lift_fst _ _ w
      have hψ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ w)
      obtain ⟨e', he', hM'⟩ := hb j R' _ _ _
        (by rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact IsLocalization.Away.algebraMap_isUnit _)
        ((h'.comp hφ).congr (by rw [spMap_comp_spMap, ← IsScalarTower.algebraMap_eq]) rfl) hψ'
        (by rw [← Category.assoc, e₁, hF])
      obtain ⟨b, hb⟩ := coord_eq_sum h' hψ' F.basis he' hM' (he.1 i) (by rw [e₁, hg]; exact (hM i).1) (hM i).2
      obtain ⟨s, hs, k, a, ha⟩ := exists_denom N (r j) g hg' b
      refine ⟨s, hs, k, a, ?_⟩
      rw [hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← smul_assoc, ha, algebraMap_smul]
    classical
    choose s hs k a h using key
    refine ⟨∏ j, s j, prod_mem fun j _ => hs j, (hL _).2 fun j => ⟨k j, (∏ l ∈ Finset.univ.erase j, s l) • a j, ?_⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), smul_smul, ← _root_.mul_assoc, _root_.mul_comm, ← smul_smul, h,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]; rfl
  · induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      exact coord_eq_sum hφ hψ F.basis he (fun i => ⟨_, hM i⟩) hu
        (by rw [hF, ← IsScalarTower.algebraMap_eq]; exact hw) hc
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul t x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨algebraMap (𝓞 K) R t • a, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul K t]

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare Matrix

private theorem valRing_loc (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) :
    ∃ _ : Algebra (𝓞 K) (AdelicDegreeTameRamification.valRing K 𝔓), IsScalarTower (𝓞 K) (AdelicDegreeTameRamification.valRing K 𝔓) K ∧
      IsLocalization 𝔓.asIdeal.primeCompl (AdelicDegreeTameRamification.valRing K 𝔓) := by
  have key : ∀ V : ValuationSubring K, 𝔓.valuationSubringAtPrime K = V →
      ∃ _ : Algebra (𝓞 K) V, IsScalarTower (𝓞 K) V K ∧ IsLocalization 𝔓.asIdeal.primeCompl V := by
    rintro _ rfl
    exact ⟨_, inferInstance,
      Localization.subalgebra.isLocalization_ofField K 𝔓.asIdeal.primeCompl 𝔓.asIdeal.primeCompl_le_nonZeroDivisors⟩
  exact key _ (HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring 𝔓)

private theorem span_loc {O R K : Type} [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra R K] [Algebra O K]
    [IsScalarTower O R K] (N : Submonoid O) [IsLocalization N R] {g m : ℕ} (L : Submodule O (Fin g → K))
    (P : Fin g → Fin g → K) (h₁ : ∀ i, ∃ s ∈ N, s • P i ∈ L)
    (h₂ : ∀ c ∈ L, ∃ a : Fin g → R, c = ∑ i, algebraMap R K (a i) • P i) (S : Submodule K (Fin g → K))
    (b : Fin m → Fin g → K) (hb : ∀ i, b i ∈ L)
    (hL : ∀ x ∈ L, x ∈ S → ∃ d ∈ N, d • x ∈ Submodule.span O (Set.range b)) (x : Fin g → K) (hx : x ∈ S) :
    (∃ a : Fin g → R, x = ∑ i, algebraMap R K (a i) • P i) ↔ ∃ β : Fin m → R, x = ∑ i, algebraMap R K (β i) • b i := by
  simp only [algebraMap_smul, eq_comm (a := x)] at h₂ ⊢
  rw [← Submodule.mem_span_range_iff_exists_fun, ← Submodule.mem_span_range_iff_exists_fun]
  constructor
  · intro h
    have h3 : ∃ d ∈ N, d • x ∈ L := by
      clear hx
      induction h using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h₁ i
      | zero => exact ⟨1, N.one_mem, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨d, hd, hx⟩ := hx
        obtain ⟨d', hd', hy⟩ := hy
        refine ⟨d * d', N.mul_mem hd hd', ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [_root_.mul_comm, mul_smul]; exact L.smul_mem _ hx
        · rw [mul_smul]; exact L.smul_mem _ hy
      | smul r x _ hx =>
        obtain ⟨d, hd, hx⟩ := hx
        obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj N r
        refine ⟨s * d, N.mul_mem s.2 hd, ?_⟩
        have : ((s : O) * d) • r • x = p • d • x := by
          rw [mul_smul, smul_comm d r, ← algebraMap_smul R (s : O), smul_smul, _root_.mul_comm, h, algebraMap_smul]
        rw [this]
        exact L.smul_mem _ hx
    obtain ⟨d, hd, hdx⟩ := h3
    obtain ⟨d', hd', h4⟩ := hL _ hdx (S.smul_of_tower_mem d hx)
    have h5 := Submodule.span_le_restrictScalars O R _ h4
    rw [Submodule.restrictScalars_mem, smul_smul, ← algebraMap_smul R] at h5
    exact (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units R ⟨_, N.mul_mem hd' hd⟩)).1 h5
  · intro h
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := h₂ _ (hb i)
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨a, ha.symm⟩

private theorem comb_iso {K : Type} [CommRing K] {A A' : Over (Sp K)} [GrpObj A] [GrpObj A'] (e : A ≅ A')
    [IsMonHom e.hom] {m : ℕ} (c : Fin m → K) (w : Fin m → (epsR K ⟶ A)) (z : epsR K ⟶ A') :
    IsLieComb c (fun i => w i ≫ e.hom) z ↔ IsLieComb c w (z ≫ e.inv) := by
  constructor
  · intro h
    simpa using DiffCoord.isLieComb_comp_hom e.inv h
  · intro h
    simpa using DiffCoord.isLieComb_comp_hom e.hom h

private theorem tan_hom {K : Type} [CommRing K] {A A' : Over (Sp K)} [GrpObj A] [GrpObj A'] (f : A ⟶ A')
    [IsMonHom f] {v : epsR K ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := DiffCoord.isTangent_comp_hom f hv

private theorem exists_model {K : Type} [Field K] [NumberField K] (F : SemiFib K) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    ∃ (G : Over (Sp (AdelicDegreeTameRamification.valRing K 𝔓))) (_ : GrpObj G) (ψ : F.P₀.A.left ⟶ G.left), IsSemiAbelian G ∧
      IsGrpPullback F.P₀.A G (spMap (algebraMap (AdelicDegreeTameRamification.valRing K 𝔓) K)) ψ ∧
      ∀ (S : Submodule K (Fin F.P₀.g → K)) (m : ℕ) (b : Fin m → Fin F.P₀.g → K),
        GlobalTheory.PtDeg.LocBasis 𝔓 (F.lieLat ⊓ S.restrictScalars (𝓞 K)) b → ∀ x ∈ S, ∀ z, IsLieComb x F.v z →
          (Integral (algebraMap (AdelicDegreeTameRamification.valRing K 𝔓) K) ψ z ↔
            ∃ β : Fin m → AdelicDegreeTameRamification.valRing K 𝔓, x = ∑ i, (β i : K) • b i) := by
  obtain ⟨_, _, _⟩ := valRing_loc K 𝔓
  have := F.P₀.isAb.comm
  obtain ⟨n, r, M, hr, -, -, hloc⟩ := cover_strong K F
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ 𝔓.asIdeal := by
    by_contra h
    push Not at h
    refine 𝔓.isPrime.ne_top (top_le_iff.1 (hr ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    exact h i
  have hp := isGrpPullback_pullback F.G (spMap (algebraMap (𝓞 K) (AdelicDegreeTameRamification.valRing K 𝔓)))
  obtain ⟨ψ, hψφ, hψ⟩ := exists_lift (IsScalarTower.algebraMap_eq (𝓞 K) (AdelicDegreeTameRamification.valRing K 𝔓) K).symm hp F.fib
  obtain ⟨e, he, hx⟩ := hloc i _ _ _ ψ (IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) _ ⟨r i, hi⟩) hp hψ hψφ
  choose e₀ he₀ hM₀ using hx
  obtain ⟨h₁, h₂⟩ := lieLat_loc K F _ 𝔓.asIdeal.primeCompl _ _ ψ e e₀ (M i) hp hψ hψφ he fun k => ⟨he₀ k, hM₀ k⟩
  have hG := IsSemiAbelian.pullback (spMap (algebraMap (𝓞 K) (AdelicDegreeTameRamification.valRing K 𝔓))) F.G F.semi
  have := hG.comm
  refine ⟨_, inferInstance, ψ, hG, hψ, fun S m b hb x hx z hz => ?_⟩
  refine Iff.trans ?_ (span_loc 𝔓.asIdeal.primeCompl F.lieLat (M i) h₁ h₂ S b (fun j => (hb.1 j).1)
    (fun y hy hy' => hb.2.2 y ⟨hy, hy'⟩) x hx)
  rw [integral_iff hψ he he₀]
  refine exists_congr fun a => ?_
  rw [comb_comb F.basis.1 hM₀, Matrix.vecMul_eq_sum]
  exact ⟨fun h => (Indep.of_basis F.basis).2 _ _ z hz h, fun h => h ▸ hz⟩

end UpperTheory.FibFin

end Cover

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

theorem UpperTheory.lie_combination_has_integral_model :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (F : GlobalTheory.LieHt.SemiFib K) (t : SAB H (Sp K)) (e : F.P₀.A ≅ t.G), IsMonHom e.hom → ∀ (m : ℕ) (u : Fin m → Fin F.P₀.g → K) (w : Fin m → (epsR K ⟶ F.P₀.A)), LinearIndependent K u → (∀ i, IsLieComb (u i) F.v (w i)) → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)), HasModel t 𝔓 ∧ ∀ (b : Fin m → Fin F.P₀.g → K) (M : Matrix (Fin m) (Fin m) K), GlobalTheory.PtDeg.LocBasis 𝔓 (F.lieLat ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)) b → (∀ i, u i = ∑ j, M i j • b j) → EigenvectorLieDegree.IsLocOrd t.G (fun i => w i ≫ e.hom) 𝔓 (vAdd 𝔓 M.det : ℝ) := by
  intro E _ _ _ H K _ _ F t e he m u w hu hw 𝔓
  have := F.P₀.isAb.comm
  obtain ⟨G, _, ψ, hG, hψ, hL⟩ := UpperTheory.FibFin.exists_model F 𝔓
  have hφ : IsGrpPullback t.G G (spMap (algebraMap (AdelicDegreeTameRamification.valRing K 𝔓) K)) (e.inv.left ≫ ψ) := by
    have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
    exact ((isGrpPullback_of_iso e.symm).comp hψ).congr (Category.id_comp _) rfl
  refine ⟨⟨G, _, _, hG, hφ⟩, fun b M hb hM => ?_⟩
  let U : Matrix (Fin m) (Fin F.P₀.g) K := u
  let B : Matrix (Fin m) (Fin F.P₀.g) K := b
  have hU : Function.Injective U.vecMul := Matrix.vecMul_injective_iff.2 hu
  have hB : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.2 hb.2.1
  have hMB : U = M * B := by
    ext i j
    rw [Matrix.mul_apply]
    simpa using congrFun (hM i) j
  have hc : ∀ c z, IsLieComb c (fun i => w i ≫ e.hom) z ↔ IsLieComb (Matrix.vecMul c U) F.v (z ≫ e.inv) := fun c z =>
    (UpperTheory.FibFin.comb_iso e c w z).trans (comb_comb (P := U) F.basis.1 hw c _)
  have alg := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  have hx : Indep (fun i => w i ≫ e.hom) :=
    ⟨fun i => UpperTheory.FibFin.tan_hom _ (alg.2.1 _ _ (hw i)),
      fun c c' z h h' => hU ((Indep.of_basis F.basis).2 _ _ _ ((hc _ _).1 h) ((hc _ _).1 h'))⟩
  have hMu : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun c c' h => hU (by
    simp only [hMB, ← Matrix.vecMul_vecMul] at h ⊢
    rw [h])
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hMu
  have hdet : (M⁻¹).det = M.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hgen : AdelicDegreeTameRamification.IsLocalGen t (fun i => w i ≫ e.hom) 𝔓 (M⁻¹).det := by
    refine ⟨G, _, _, M⁻¹, hG, hφ, fun c => ?_, rfl, by rw [hdet]; exact inv_ne_zero hd.ne_zero⟩
    have hS : Matrix.vecMul c U ∈ Submodule.span K (Set.range u) := by
      rw [Matrix.vecMul_eq_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hI : ∀ z : epsR K ⟶ t.G, GlobalTheory.FlatDegreeCompare.Integral (algebraMap (AdelicDegreeTameRamification.valRing K 𝔓) K) (e.inv.left ≫ ψ) z ↔
        GlobalTheory.FlatDegreeCompare.Integral (algebraMap (AdelicDegreeTameRamification.valRing K 𝔓) K) ψ (z ≫ e.inv) := fun z => by
      refine exists_congr fun y => and_congr_right fun _ => ?_
      exact Eq.congr_left (Category.assoc _ _ _).symm
    have h1 : ∀ β : Fin m → AdelicDegreeTameRamification.valRing K 𝔓, (Matrix.vecMul c U = ∑ i, (β i : K) • b i) ↔
        c = Matrix.vecMul (fun i => (β i : K)) M⁻¹ := fun β => by
      have : ∑ i, (β i : K) • b i = Matrix.vecMul (Matrix.vecMul (fun i => (β i : K)) M⁻¹) U := by
        rw [hMB, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.vecMul_eq_sum]
      rw [this]
      exact hU.eq_iff
    rw [mem_latticeCoords]
    simp only [hc, hI, ← h1]
    constructor
    · rintro ⟨z, hz, hi⟩
      exact (hL _ m b hb _ hS _ hz).1 hi
    · intro h
      obtain ⟨z, hz, -⟩ := alg.1 (Matrix.vecMul c U)
      refine ⟨z ≫ e.hom, ?_⟩
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
      exact ⟨hz, (hL _ m b hb _ hS _ hz).2 h⟩
  have := locOrd_of_gen hx hgen
  rw [hdet, map_inv₀, WithZero.log_inv] at this
  exact this
