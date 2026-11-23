import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

noncomputable section Cover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.LieGlue GlobalTheory.CM.LieLoc GlobalTheory.LieHt

namespace UpperTheory.LatDRSpan

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

open Formalism.L2.Pj GlobalTheory.ShFam.Pad in

private theorem comb_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) {n : ℕ} {c : Fin n → S} {v : Fin n → (epsR S ⟶ G')}
    {w : epsR S ⟶ G'} (h : IsLieComb c v w) : IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := by
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩

open Formalism.MainNotions.DIV.Cons (intO) in

private theorem norm_int_le {K C : Type} [Field K] [NumberField K] [NontriviallyNormedField C] [IsUltrametricDist C]
    (j : K →+* C) (a : 𝓞 K) : ‖j (algebraMap (𝓞 K) K a)‖ ≤ 1 := by
  have := GlobalTheory.ShFam.Pad.Guard.intO_valRing C
  have := GlobalTheory.ShFam.Pad.Guard.intO_frac C
  have h1 : IsIntegral (intO C) (j.comp (algebraMap (𝓞 K) K) a) :=
    (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) _ (RingHom.ext_int _ _)
  classical
  let _ : GCDMonoid (intO C) := IsBezout.toGCDDomain _
  have : IsIntegrallyClosed (intO C) := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := intO C) (K := C)).1 h1
  have hb' : (b : C) = j (algebraMap (𝓞 K) K a) := hb
  exact hb' ▸ b.2

private theorem exists_norm_one {K C : Type} [Field K] [NumberField K] [NontriviallyNormedField C] [IsUltrametricDist C]
    (j : K →+* C) {n : ℕ} (r : Fin n → 𝓞 K) (hr : Ideal.span (Set.range r) = ⊤) :
    ∃ i, ‖j (algebraMap (𝓞 K) K (r i))‖ = 1 := by
  by_contra h
  push Not at h
  have h1 : (1 : 𝓞 K) ∈ Ideal.span (Set.range r) := hr ▸ Submodule.mem_top
  have key : ∀ x ∈ Ideal.span (Set.range r), ‖j (algebraMap (𝓞 K) K x)‖ < 1 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact lt_of_le_of_ne (norm_int_le j _) (h i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
    | smul s x _ hx =>
      rw [smul_eq_mul, map_mul, map_mul, norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le j s) (norm_nonneg _) hx
  simpa using key 1 h1

open Formalism.MainNotions.DIV.Cons (intO) in

private theorem local_basis {K C : Type} [Field K] [NumberField K] [NontriviallyNormedField C] [IsUltrametricDist C]
    (F : SemiFib K) (j : K →+* C) :
    ∃ (R : Type) (_ : CommRing R) (f : 𝓞 K →+* R) (g : R →+* K) (ρ : R →+* ↥(intO C)) (G : Over (Sp R)) (_ : GrpObj G)
      (π : G.left ⟶ F.G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A))
      (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), g.comp f = algebraMap (𝓞 K) K ∧ (intO C).subtype.comp ρ = j.comp g ∧
      IsGrpPullback G F.G (spMap f) π ∧ IsLieBasis e ∧
      (∀ k, (e₀ k).left ≫ F.φ = spMap (Chart.dualMapR g) ≫ (e k).left ≫ π ∧ IsLieComb (M k) F.v (e₀ k)) ∧
      (∀ k, ∃ s : K, ‖j s‖ = 1 ∧ s • M k ∈ F.lieLat) ∧
      ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, g (a i) • M i := by
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := cover_strong K F
  obtain ⟨i, hi⟩ := exists_norm_one j r hr
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  let R := Localization.Away (r i)
  have hu : IsUnit (algebraMap (𝓞 K) K (r i)) := ((map_ne_zero_iff _ hinj).2 (hM i).1).isUnit
  let g : R →+* K := IsLocalization.Away.lift (r i) hu
  have hg : g.comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K := IsLocalization.Away.lift_comp _ _
  let _ : Algebra R K := g.toAlgebra
  have : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hg x).symm
  have hval : ∀ z : R, j.comp g z ∈ intO C := fun z => by
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r i)) z
    have hz := congrArg (fun q => ‖j (g q)‖) (IsLocalization.mk'_spec R x s)
    obtain ⟨m, hm⟩ := s.2
    have h1 : ∀ x, g (algebraMap (𝓞 K) R x) = algebraMap (𝓞 K) K x := RingHom.congr_fun hg
    have hs : ‖j (algebraMap (𝓞 K) K s)‖ = 1 := by
      rw [← hm]; simp only [map_pow, norm_pow, hi, one_pow]
    simp only [map_mul, norm_mul, h1, hs, _root_.mul_one] at hz
    exact hz.trans_le (norm_int_le j x)
  have hp := isGrpPullback_pullback F.G (spMap (algebraMap (𝓞 K) R))
  obtain ⟨ψ, hψφ, hψ⟩ := exists_lift hg hp F.fib
  obtain ⟨e, he, hx⟩ := hloc i R _ _ ψ (IsLocalization.Away.algebraMap_isUnit _) hp hψ hψφ
  choose e₀ he₀ hM₀ using hx
  obtain ⟨h₁, h₂⟩ := lieLat_loc K F R (Submonoid.powers (r i)) _ _ ψ e e₀ (M i) hp hψ hψφ he fun k => ⟨he₀ k, hM₀ k⟩
  refine ⟨R, inferInstance, algebraMap _ _, g, (j.comp g).codRestrict _ hval, _, inferInstance, _, e, e₀, M i, hg, rfl,
    hp, he, fun k => ⟨?_, hM₀ k⟩, fun k => ?_, h₂⟩
  · rw [← hψφ, ← Category.assoc, he₀ k, Category.assoc]
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := h₁ k
    refine ⟨algebraMap (𝓞 K) K (r i ^ m), by simp only [map_pow, norm_pow, hi, one_pow], ?_⟩
    rwa [algebraMap_smul]

open Formalism.L2.Pj GlobalTheory.ShFam.Pad in
open Formalism.MainNotions.DIV.Cons (intO) in

private theorem mem_latDR_iff_span {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) (hX : X.IsSeparated)
    {K C : Type} [Field K] [NumberField K] [NontriviallyNormedField C] [IsUltrametricDist C]
    (F : SemiFib K) (j : K →+* C) (yO : Sp (𝓞 K) ⟶ X) (ψ : F.G.left ⟶ t.G.left) (hψ : IsGrpPullback F.G t.G yO ψ)
    (c : Fin F.P₀.g → C) (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO)
      (fun k => spMap (dualMap j) ≫ (F.v k).left ≫ F.φ ≫ ψ) c w) :
    w ∈ latDR t (spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO) ↔
      ∃ (n : ℕ) (a : Fin n → C) (v : Fin n → Fin F.P₀.g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ F.lieLat) ∧
        c = ∑ m, a m • fun i => j (v m i) := by
  obtain ⟨R, _, f, g, ρ, G, _, π, e, e₀, M, hg, hρ, hπ, he, hM, h₁, h₂⟩ := local_basis F j
  have hpR := hπ.comp hψ
  have hpK := F.fib.comp hψ
  obtain ⟨bR, bR'⟩ := ((GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ hpR).2 _ e).1 he
  obtain ⟨bK, bK'⟩ := ((GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ hpK).2 _ F.v).1 F.basis
  obtain ⟨bC, bC'⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t j _ _ _ bK bK'
  have hE : GlobalTheory.LineNorm.IsTanBasis t (spMap f ≫ yO) (fun k => (e k).left ≫ π ≫ ψ) :=
    ⟨bR, fun T _ φ => (GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ _ _ _ bR bR').2⟩
  have hx : spMap (intO C).subtype ≫ spMap ρ ≫ spMap f ≫ yO = spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO := by
    rw [← Category.assoc, spMap_comp_spMap, hρ, ← hg, ← spMap_comp_spMap, ← spMap_comp_spMap]
    simp only [Category.assoc]
  have hv : ∀ k, spMap (dualMap ((intO C).subtype.comp ρ)) ≫ (e k).left ≫ π ≫ ψ =
      spMap (dualMap j) ≫ (e₀ k).left ≫ F.φ ≫ ψ := fun k => by
    rw [hρ, ← GlobalTheory.HTPres.bc_bc, ← Category.assoc (e₀ k).left, (hM k).1]
    simp only [Category.assoc]
    rfl
  have key := GlobalTheory.HTPres.mem_latDR_iff t hX _ hE C ρ
  simp only [hx, hv] at key
  have hA : ∀ k, IsCombAtG t (spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO)
      (fun k => spMap (dualMap j) ≫ (F.v k).left ≫ F.φ ≫ ψ) (fun i => j (M k i))
      (spMap (dualMap j) ≫ (e₀ k).left ≫ F.φ ≫ ψ) := fun k =>
    GlobalTheory.LatDRFree.comb_map t j (comb_push t _ _ _ hpK (hM k).2)
  have lin : ∀ cf w', IsCombAtG t (spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO)
      (fun k => spMap (dualMap j) ≫ (e₀ k).left ≫ F.φ ≫ ψ) cf w' →
      IsCombAtG t (spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO)
        (fun k => spMap (dualMap j) ≫ (F.v k).left ≫ F.φ ≫ ψ) (fun i => ∑ k, cf k * j (M k i)) w' := fun cf w' h => by
    have h' := tanLinG _ bC _ (Matrix.of fun i k => j (M k i)) cf w' hA h
    have e' : (Matrix.of fun i k => j (M k i)).mulVec cf = fun i => ∑ k, cf k * j (M k i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, _root_.mul_comm]
    rwa [e'] at h'
  have ht := GlobalTheory.FlagEmb.comb_tan t bC hw
  constructor
  · intro hd
    have hx' : spMap ((intO C).subtype.comp ρ) ≫ spMap f ≫ yO = spMap j ≫ spMap (algebraMap (𝓞 K) K) ≫ yO := by
      rw [← hx, ← spMap_comp_spMap, Category.assoc]
    have hb := hE.2 C ((intO C).subtype.comp ρ) w (by rw [hx']; exact ht)
    simp only [hx', hv] at hb
    obtain ⟨cf, hcf, -⟩ := hb
    have hn := (key cf w hcf).1 hd
    choose s hs hsM using h₁
    refine ⟨_, fun k => cf k * (j (s k))⁻¹, fun k => s k • M k, fun k => ?_, hsM, ?_⟩
    · rw [norm_mul, norm_inv, hs, inv_one, _root_.mul_one]; exact hn k
    · rw [(bC' w ht).unique hw (lin cf w hcf)]
      funext i
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h0 : j (s k) ≠ 0 := fun h0 => by simpa [h0] using hs k
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      field_simp
  · rintro ⟨n, a, v, ha, hvL, rfl⟩
    choose b hb using fun m => h₂ _ (hvL m)
    have hb1 : ∀ z, j (g z) = (ρ z : C) := fun z => (RingHom.congr_fun hρ z).symm
    let cf : Fin F.P₀.g → ↥(intO C) := fun k => ∑ m, (⟨a m, ha m⟩ : ↥(intO C)) * ρ (b m k)
    obtain ⟨w', -, hw'⟩ := GlobalTheory.FlagEmb.exists_comb t (fun k => GlobalTheory.FlagEmb.comb_tan t bC (hA k)) fun k => (cf k : C)
    have h' := lin _ _ hw'
    have e' : (fun i => ∑ k, (cf k : C) * j (M k i)) = ∑ m, a m • fun i => j (v m i) := by
      funext i
      simp only [cf, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Finset.sum_mul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, hb, map_sum, map_mul, hb1, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm
    rw [e'] at h'
    obtain rfl := GlobalTheory.FlagEmb.comb_unique t bC hw h'
    exact (key _ _ hw').2 fun k => (cf k).2

end UpperTheory.LatDRSpan

end Cover

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

theorem UpperTheory.dual_number_tangent_coordinates :
    ∀ (D : D7) (O : Setup D) (y : Pt O.s) (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb), FibTie O y F ι → ∀ (p : ℕ) [Fact p.Prime] (io : Qb →+* ℂ_[p]) (U : Fin F.P₀.g → (Sp (DualNumber ℂ_[p]) ⟶ O.s.T.Z.t.G.left)), (∀ (k : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some x → U k = spMap (dualMap io) ≫ y.u x.1 x.2) → ∀ (c : Fin F.P₀.g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ O.s.T.Z.t.G.left), IsCombAtG O.s.T.Z.t (spMap io ≫ y.y ≫ genι O.s.T.Z) U c w → (w ∈ latDR O.s.T.Z.t (spMap io ≫ y.y ≫ genι O.s.T.Z) ↔ ∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin F.P₀.g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ F.lieLat) ∧ c = ∑ m, a m • fun i => io (ι (v m i))) := by
  intro D O y K _ _ F ι hT p _ io U hU c w hw
  obtain ⟨jF, yO, ψ, -, hy, hψ, -, hg, hu⟩ := hT
  have hX : O.s.T.Z.X.IsSeparated := by
    have : IsProper O.s.T.Z.s := by exact isProper_toroidalModel_structureMap O.s.T.Z
    exact ⟨by rw [← Limits.terminal.comp_from O.s.T.Z.s]; infer_instance⟩
  have hx : spMap io ≫ y.y ≫ genι O.s.T.Z = spMap (io.comp ι) ≫ spMap (algebraMap (𝓞 K) K) ≫ yO := by
    rw [← hy, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
    simp only [Category.assoc]
  have hU' : U = fun k => spMap (dualMap (io.comp ι)) ≫ (F.v k).left ≫ F.φ ≫ ψ := by
    funext k
    have hk : (k : ℕ) < (letters O.S.Dw).length := hg ▸ k.2
    have hx := List.getElem?_eq_getElem hk
    rw [hU k _ hx, hu k _ hx, ← GlobalTheory.HTPres.bc_bc]
    rfl
  rw [hx, hU'] at hw
  rw [hx]
  exact UpperTheory.LatDRSpan.mem_latDR_iff_span _ hX F (io.comp ι) yO ψ hψ c w hw
