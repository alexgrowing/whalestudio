import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtLift

theorem exists_etale_to_affineSpace {k : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec k) [Smooth f]
    (x : X) : ∃ (V : X.Opens) (n : ℕ) (u : V.toScheme ⟶ 𝔸(Fin n; Spec k)), x ∈ V ∧ Etale u ∧
      u ≫ (𝔸(Fin n; Spec k) ↘ Spec k) = V.ι ≫ f := by
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hs
  have hmap : Etale (AffineSpace.map (Fin n) hU.fromSpec) :=
    MorphismProperty.of_isPullback (P := @Etale) (AffineSpace.isPullback_map (n := Fin n) hU.fromSpec).flip inferInstance
  have hSg : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.mpr hg
  refine ⟨V, n, hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫ (AffineSpace.SpecIso (Fin n) _).inv ≫
    AffineSpace.map (Fin n) hU.fromSpec, hxV, inferInstance, ?_⟩
  simp only [Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hgC]
  rw [CommRingCat.ofHom_hom, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, hV.isoSpec_hom_fromSpec_assoc]

theorem exists_surjective_appTop {Y P : Scheme.{0}} (j : Y ⟶ P) [IsImmersion j] (y : Y) (U : Y.Opens)
    (hy : y ∈ U) : ∃ W : P.Opens, j y ∈ W ∧ j ⁻¹ᵁ W ≤ U ∧ Function.Surjective (j ∣_ W).appTop := by
  obtain ⟨O, hO, hOU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  have hyC : j y ∈ (j.coborderRange : Set P) := subset_coborder ⟨y, rfl⟩
  have hyO : j y ∈ O := by
    rw [← Set.mem_preimage, hOU]; exact hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWs⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
    (show j y ∈ O ∩ (j.coborderRange : Set P) from ⟨hyO, hyC⟩) (hO.inter j.coborderRange.isOpen)
  refine ⟨W, hxW, ?_, ?_⟩
  · intro z hz
    show z ∈ (U : Set Y)
    rw [← hOU]
    exact (hWs hz).1
  · have : IsAffine W := hW
    have key : Set.range (j ∣_ W) = (Scheme.Opens.ι W) ⁻¹' closure (Set.range j) := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        apply subset_closure
        refine ⟨(j ⁻¹ᵁ W).ι z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
      · intro hx
        have hxW' : (Scheme.Opens.ι W) x ∈ (W : Set P) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
        have hxC : (Scheme.Opens.ι W) x ∈ (j.coborderRange : Set P) := (hWs hxW').2
        have h3 : (Scheme.Opens.ι W) x ∈ closure (Set.range j) ∩ coborder (Set.range j) := ⟨hx, hxC⟩
        rw [closure_inter_coborder] at h3
        obtain ⟨z, hz⟩ := h3
        have hzW : z ∈ j ⁻¹ᵁ W := by
          show j z ∈ W; rw [hz]; exact hxW'
        obtain ⟨z', hz'⟩ : z ∈ Set.range (j ⁻¹ᵁ W).ι := by
          rw [Scheme.Opens.range_ι]; exact hzW
        refine ⟨z', (Scheme.Opens.ι W).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hz', hz]
    have : IsClosedImmersion (j ∣_ W) := by
      refine .of_isPreimmersion _ ?_
      rw [key]
      exact isClosed_closure.preimage (Scheme.Opens.ι W).continuous
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (j ∣_ W)).2

end GlobalTheory.Mum.EtLift

open GlobalTheory.Mum.EtLift in

theorem GlobalTheory.Mum.exists_etale_coords_lift_immersion : ∀ (R : Type) [CommRing R] [IsLocalRing R] (N : ℕ) (Y : Over (Sp (ResidueField R))), Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N), IsImmersion j → j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → ∀ y : Y.left, ∃ (W0 : (PSpace R N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O ∧ (O : Set Y.left) ⊆ j ⁻¹' W0 ∧ τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R N ∧ Etale e ∧ e ≫ pullback.snd _ _ = O.ι ≫ Y.hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0 := by
  intro R _ _ N Y hsm j hj hjs y
  have : Smooth Y.hom := hsm
  obtain ⟨V, g, u, hyV, hu, huo⟩ := exists_etale_to_affineSpace (k := CommRingCat.of (ResidueField R)) Y.hom y
  have huo' : u ≫ (𝔸(Fin g; Sp (ResidueField R)) ↘ Sp (ResidueField R)) = V.ι ≫ Y.hom := huo
  obtain ⟨W, hyW, hWV, hsurj⟩ := exists_surjective_appTop j y V hyV
  let u' : (j ⁻¹ᵁ W).toScheme ⟶ 𝔸(Fin g; Sp (ResidueField R)) := Y.left.homOfLE hWV ≫ u
  have hu' : Etale u' := by
    have : Etale (Y.left.homOfLE hWV) := inferInstance
    exact inferInstanceAs (Etale (Y.left.homOfLE hWV ≫ u))
  choose s hs using fun i : Fin g => hsurj (u'.appTop (AffineSpace.coord (Sp (ResidueField R)) i))
  let τ0 : W.toScheme ⟶ 𝔸(Fin g; Sp R) := AffineSpace.homOfVector (W.ι ≫ PSpace.str R N) s
  have hP := AffineSpace.isPullback_map (n := Fin g) (spMap (residue R))
  have hfst : u' ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.map_over, τ0, AffineSpace.homOfVector_over, u']
      rw [reassoc_of% huo', Scheme.homOfLE_ι_assoc, ← Category.assoc (j ∣_ W), morphismRestrict_ι,
        Category.assoc, hjs]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, τ0,
        AffineSpace.homOfVector_appTop_coord]
      exact (hs i).symm
  refine ⟨W, g, τ0, j ⁻¹ᵁ W, u' ≫ hP.isoPullback.hom, hyW, fun z hz => hz,
    AffineSpace.homOfVector_over _ _, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, u']
    rw [huo', Scheme.homOfLE_ι_assoc]
  · intro T t w hw
    have hfst' : Y.left.homOfLE hWV ≫ u ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
      rw [← Category.assoc]; exact hfst
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [hfst', ← Category.assoc]
    congr 1
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, hw]
