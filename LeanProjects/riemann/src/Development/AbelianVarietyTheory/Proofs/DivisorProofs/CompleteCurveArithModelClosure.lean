import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

theorem le_dim_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → (((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W) := by
  intro F _ _ W G _ q g s d hq _ hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hgen : ∀ x, t (g x) = genericPoint (Sp ℤ) := by
    intro x
    rw [genericPoint_eq_bot_of_affine]
    have e : g ≫ t = s ≫ spMap ((algebraMap (𝓞 F) F).comp (Int.castRingHom (𝓞 F))) := by
      simp only [t, ← Category.assoc, hpb.w]
      simp [spMap, Spec.map_comp]
    change (g ≫ t) x = _
    rw [e]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap _ (s x).asIdeal = ⊥
    have hp : (show PrimeSpectrum F from s x).asIdeal.IsPrime := (show PrimeSpectrum F from s x).isPrime
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from s x).asIdeal]
    exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
  have key := GlobalTheory.Vert.dim_add_dim_le (S := W) (T := Sp ℤ) (W := G) t.isClosedMap g.continuous
    g.isEmbedding.injective hgen
  have hZ : topologicalKrullDim (Sp ℤ) = 1 := by
    change topologicalKrullDim (PrimeSpectrum ℤ) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  rw [hd, hZ] at key
  exact_mod_cast key

theorem dim_le_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
  intro F _ _ W G _ q g s d hq hc hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  have : Flat t := (flat_int_iff_charZero t).2 hc
  have : LocallyOfFiniteType t := inferInstance
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  obtain ⟨he, hr⟩ := isEmbedding_and_range_eq_of_isPullback q hpb

  have hfib : Set.range g = t ⁻¹' {genericPoint (Sp ℤ)} := by
    rw [hr, genericPoint_eq_bot_of_affine]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy⟩
      change Spec.map _ (q x) = _
      rw [← hy]
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ (Ideal.comap _ (show PrimeSpectrum F from y).asIdeal) = ⊥
      have hp : (show PrimeSpectrum F from y).asIdeal.IsPrime := (show PrimeSpectrum F from y).isPrime
      rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from y).asIdeal, Ideal.comap_comap]
      exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
    · intro h
      have h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ :=
        congrArg PrimeSpectrum.asIdeal h
      have h0 : (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot h'
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ ⊥ = (show PrimeSpectrum (𝓞 F) from q x).asIdeal
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)

  obtain ⟨A, _, _, instA, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq t (genericPoint W)
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain ⟨d', hd'⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  have hfd := topologicalKrullDim_preimage_genericPoint_eq t (d := d') (hA ▸ hd')
  rw [← hfib, topologicalKrullDim_eq_of_isEmbedding he rfl, hd] at hfd
  have hdd : d' = d := by exact_mod_cast hfd.symm
  subst hdd
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
  refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
  have hdB : Algebra.trdeg ℤ B = d' := hB.trans (hA.symm.trans hd')
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
  refine (add_le_add hZ1 (le_refl ((d' : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem dim_eq_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W = (d + 1 : ℕ) :=
  fun F _ _ W G _ q g s d h₁ h₂ h₃ h₄ =>
    le_antisymm (dim_le_of_genFibre F W G q g s d h₁ h₂ h₃ h₄) (le_dim_of_genFibre F W G q g s d h₁ h₂ h₃ h₄)

theorem exists_closure_arith_surface : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∃ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ P.p) 1 ∧ z ≫ w = redι Z ≫ P.j ∧ IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) := by
  intro F _ _ Y P Z hZ
  let S : Closeds P.X := ⟨closure (P.j '' (Z : Set Y.X)), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set P.X) := (hZ.isIrreducible.image _ P.j.continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion P.j := MorphismProperty.of_isPullback P.pb.flip inferInstance
  have hpb1 : IsPullback (pullback.fst w P.j) (pullback.snd w P.j ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := (IsPullback.of_hasPullback w P.j).paste_vert P.pb
  haveI : IsReduced (pullback (w ≫ P.p) (spMap (algebraMap (𝓞 F) F))) :=
    isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _
  haveI : IsReduced (pullback w P.j) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w P.j) = (Z : Set Y.X) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change P.j ⁻¹' closure (P.j '' (Z : Set Y.X)) = _
    rw [← P.j.isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w P.j) Z hrange
  have hzw : (e.hom ≫ pullback.fst w P.j) ≫ w = redι Z ≫ P.j := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : F →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ Y.str).appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w P.j).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ P.p) := by
    obtain ⟨N, j, _, hj⟩ := P.ar.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  have hdim := dim_eq_of_genFibre F _ _ (w ≫ P.p) (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) 1 hproj hcW hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w P.j, inferInstance, P.ar.of_isClosedImmersion w hcW hdim, hzw, hpb⟩

end GlobalTheory.CurveClosure
