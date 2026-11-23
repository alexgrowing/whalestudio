import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HolomorphicLefschetzFiniteEtaleIntegral
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsIntegralClopenDecompositionOfSmooth
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CompactSpaceOfProjectiveAndOfFinite
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothOfRelativeDimensionCompEtale
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceEqSumClopenDecomposition
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsTangentMatrixIffRestrictOpen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUniqueComplexPointLiftClopenCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteDimensionalHodgeCohomologyOfSmoothProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

private theorem isAffine_of_iso {Z Z' : Scheme.{0}} (e : Z' ⟶ Z) [IsIso e] {U : Z.Opens}
    (h : IsAffineOpen (e ⁻¹ᵁ U)) : IsAffineOpen U := by
  have h' := h.preimage (inv e)
  have e' : (inv e) ⁻¹ᵁ (e ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id, Scheme.Hom.id_preimage]
  rwa [e'] at h'

private theorem isTan_of_iso {Z Z' Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (e : Z' ⟶ Z) [IsIso e]
    (d : ℕ) (c1 c2 : Y ⟶ Z') (a1 a2 : Y ⟶ Z) (e1 : c1 ≫ e = a1) (e2 : c2 ≫ e = a2)
    (h1 : c1 ≫ e ≫ s = s') (h2 : c2 ≫ e ≫ s = s') (g1 : a1 ≫ s = s') (g2 : a2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ)
    (hT : IsTan (s := e ≫ s) d c1 c2 h1 h2 y A) : IsTan (s := s) d a1 a2 g1 g2 y A := by
  subst e1 e2
  obtain ⟨U', V, hV1, hV2, t, hy, hU', hV, φ, p1, p2, p3, p4⟩ := hT
  obtain ⟨U, rfl⟩ : ∃ U : Z.Opens, U' = e ⁻¹ᵁ U := ⟨e ''ᵁ U', (e.preimage_image_eq U').symm⟩
  have hs : ∀ x : Sec (e ≫ s) (e ⁻¹ᵁ U), ∃ x' : Sec s U, appSec s (e ≫ s) e U x' = x :=
    fun x => (ConcreteCategory.bijective_of_isIso (e.app U)).2 x
  choose r hr using hs
  have hc : ∀ (c : Y ⟶ Z') (x : Sec (e ≫ s) (e ⁻¹ᵁ U)),
      appSec s s' (c ≫ e) U (r x) = appSec (e ≫ s) s' c (e ⁻¹ᵁ U) x := by
    intro c x
    conv_rhs => rw [← hr x]
    simp only [appSec, Scheme.Hom.comp_app]
    rfl
  refine ⟨U, V, hV1, hV2, fun l => r (t l), hy, isAffine_of_iso e hU', hV, φ, p1, fun l => ?_, fun j => ?_, p4⟩
  · rw [hc]; exact p2 l
  · rw [hc]; exact p3 j

theorem UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_correspondence :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  intro Z _ s d _ hP Y s' c1 c2 h1 h2 _ _ hf2 he2 F hF A hA a
  classical
  haveI := hf2
  haveI := he2
  haveI cZ : CompactSpace Z := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.1 Z s hP
  haveI cY : CompactSpace Y := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.2 Y Z c1 inferInstance cZ
  haveI sm : SmoothOfRelativeDimension d s' := UpperTheory.Cb.smoothOfRelativeDimension_comp_etale Z Y s s' c1 h1 d inferInstance
  obtain ⟨J, _, W, hdis, hsup, hint⟩ := UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth Y s' d
  have hcov : ∀ y : Y, ∃ i, y ∈ W i := fun y => by
    have : y ∈ iSup W := by rw [hsup]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hne : ∀ {i j : J} {y : Y}, y ∈ W i → y ∈ W j → i = j := by
    intro i j y hi hj
    by_contra hij
    have : y ∈ W i ⊓ W j := ⟨hi, hj⟩
    rw [hdis i j hij] at this
    exact this
  have hcl : ∀ m, IsClosed (W m : Set Y) := by
    intro m
    have e : ((W m : Set Y))ᶜ = ⋃ i ∈ {i | i ≠ m}, (W i : Set Y) := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · intro hy
        obtain ⟨i, hi⟩ := hcov y
        exact ⟨i, fun e => hy (e ▸ hi), hi⟩
      · rintro ⟨i, him, hi⟩ hy
        exact him (hne hi hy)
    rw [← isOpen_compl_iff, e]
    exact isOpen_biUnion fun i _ => (W i).isOpen
  haveI instI : ∀ m, IsClosedImmersion (W m).ι := fun m =>
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl m)
  haveI instF1 : ∀ m, IsFinite ((W m).ι ≫ c1) := fun m => inferInstance
  haveI instF2 : ∀ m, IsFinite ((W m).ι ≫ c2) := fun m => inferInstance
  haveI instE1 : ∀ m, Etale ((W m).ι ≫ c1) := fun m => inferInstance
  haveI instE2 : ∀ m, Etale ((W m).ι ≫ c2) := fun m => inferInstance
  have hm1 : ∀ m, ((W m).ι ≫ c1) ≫ s = (W m).ι ≫ s' := fun m => by rw [Category.assoc, h1]
  have hm2 : ∀ m, ((W m).ι ≫ c2) ≫ s = (W m).ι ≫ s' := fun m => by rw [Category.assoc, h2]
  let φ : ∀ m, CxPts ((W m).ι ≫ s') (RingHom.id ℂ) → CxPts s' (RingHom.id ℂ) := fun m y' =>
    ⟨y'.1 ≫ (W m).ι, by simpa [Category.assoc] using y'.2⟩
  have φinj : ∀ m, Function.Injective (φ m) := by
    intro m y y' e
    have e' : y.1 ≫ (W m).ι = y'.1 ≫ (W m).ι := congrArg Subtype.val e
    exact Subtype.ext ((cancel_mono _).1 e')
  let Fm : ∀ m, Finset (CxPts ((W m).ι ≫ s') (RingHom.id ℂ)) := fun m =>
    F.preimage (φ m) (φinj m).injOn
  have hFm : ∀ m y', y' ∈ Fm m ↔ y'.1 ≫ (W m).ι ≫ c1 = y'.1 ≫ (W m).ι ≫ c2 := by
    intro m y'
    rw [Finset.mem_preimage, hF]
    simp only [φ, Category.assoc]
  have hAm : ∀ m, ∀ y' ∈ Fm m, GlobalTheory.W1.IsTan d ((W m).ι ≫ c1) ((W m).ι ≫ c2) (hm1 m) (hm2 m) y' (A (φ m y')) ∧
      (1 - A (φ m y')).det ≠ 0 := by
    intro m y' hy'
    obtain ⟨hT, hD⟩ := hA (φ m y') (Finset.mem_preimage.1 hy')
    refine ⟨?_, hD⟩
    haveI : IsIso (⊤ : Z.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e1 : (((W m).ι ≫ c1) ≫ inv (⊤ : Z.Opens).ι) ≫ (⊤ : Z.Opens).ι = (W m).ι ≫ c1 := by simp
    have e2 : (((W m).ι ≫ c2) ≫ inv (⊤ : Z.Opens).ι) ≫ (⊤ : Z.Opens).ι = (W m).ι ≫ c2 := by simp
    have hT' := (UpperTheory.Cb.isTangentMatrix_iff_restrict_open Z Y s s' d c1 c2 h1 h2 ⊤ (W m) _ _ e1 e2 (φ m y') y' rfl (A (φ m y'))).1 hT
    exact isTan_of_iso (⊤ : Z.Opens).ι d _ _ _ _ e1 e2 _ _ _ _ y' _ hT'
  let g : CxPts s' (RingHom.id ℂ) → ℂ := fun y =>
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det
  have key : ∀ m, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace (hm1 m) a b ∘ₗ hodgePull (hm2 m) a b) =
        ∑ y ∈ Fm m, g (φ m y) := fun m => by
    haveI := hint m
    exact UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_integral Z s d hP (W m).toScheme ((W m).ι ≫ s') ((W m).ι ≫ c1) ((W m).ι ≫ c2) (hm1 m) (hm2 m)
      inferInstance inferInstance (Fm m) (hFm m) (fun y' => A (φ m y')) (hAm m) a
  have hFD : ∀ b, FiniteDimensional ℂ (hodgeH s a b) := by
    rcases isEmpty_or_nonempty J with hJ | ⟨⟨m⟩⟩
    · exact fun b => UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj Z s d hP a b
    · exact (key m).1
  refine ⟨hFD, ?_⟩
  have hu : ∀ b, hodgeTrace h1 a b ∘ₗ hodgePull h2 a b =
      ∑ m, hodgeTrace (hm1 m) a b ∘ₗ hodgePull (hm2 m) a b := by
    intro b
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, UpperTheory.Cb.hodgeTrace_eq_sum_clopen_decomposition Z Y s s' c1 h1 J W hdis hsup instF1 instE1 a b (hodgePull h2 a b x),
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.comp_apply, hodgePull_comp h2 rfl (hm2 m) a b x]
  have hsum : ∑ m, ∑ y ∈ Fm m, g (φ m y) = ∑ y ∈ F, g y := by
    have hP9 : ∀ y : CxPts s' (RingHom.id ℂ), ∃ m, ∃ y', φ m y' = y := fun y => by
      obtain ⟨m, ⟨y', hy', -⟩, -⟩ := UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover Y s' J W hdis hsup y
      exact ⟨m, y', Subtype.ext hy'⟩
    have hU9 : ∀ {m m' y' y''}, φ m y' = φ m' y'' → m = m' := by
      intro m m' y' y'' e
      obtain ⟨m0, -, hu0⟩ := UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover Y s' J W hdis hsup (φ m y')
      have a1 := hu0 m ⟨y', rfl, fun z hz => φinj m (Subtype.ext hz)⟩
      have a2 := hu0 m' ⟨y'', (congrArg Subtype.val e).symm, fun z hz => φinj m' (Subtype.ext (hz.trans (congrArg Subtype.val e)))⟩
      exact a1.trans a2.symm
    choose μ y0 hy0 using hP9
    rw [← Finset.sum_fiberwise F μ g]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_nbij (φ m) ?_ (φinj m).injOn ?_ (fun _ _ => rfl)
    · intro y' hy'
      refine Finset.mem_filter.2 ⟨Finset.mem_preimage.1 hy', ?_⟩
      exact hU9 (hy0 (φ m y'))
    · intro y hy
      obtain ⟨hyF, rfl⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      exact ⟨y0 y, Finset.mem_coe.2 (Finset.mem_preimage.2 (by rw [hy0]; exact hyF)), hy0 y⟩
  change _ = ∑ y ∈ F, g y
  rw [← hsum, ← Finset.sum_congr rfl (fun m _ => (key m).2), Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hu b, map_sum, Finset.mul_sum]
