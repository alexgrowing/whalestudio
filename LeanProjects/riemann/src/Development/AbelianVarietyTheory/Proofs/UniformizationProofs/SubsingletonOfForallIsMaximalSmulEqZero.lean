import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false in

theorem acyclic_extendScalars_of_flat {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hC : C.Acyclic) :
    (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).Acyclic := by
  have : QuasiIso (0 : C ⟶ C) := ⟨fun p => (quasiIsoAt_iff_exactAt _ p (hC p)).2 (hC p)⟩
  have h := GlobalTheory.quasiIso_extendScalars_of_flat (0 : C ⟶ C) hflat hflat n hn hn g
  rw [Functor.map_zero] at h
  intro p
  have h' := (quasiIsoAt_iff_isIso_homologyMap _ p).1 (h.1 p)
  rw [HomologicalComplex.homologyMap_zero] at h'
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isIsoZero_iff_source_target_isZero _ _).1 h' |>.1

theorem subsingleton_of_forall_isMaximal_smul_eq_zero {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (h : ∀ P : Ideal R, P.IsMaximal → ∃ r, r ∉ P ∧ ∀ z : M, r • z = 0) :
    Subsingleton M := by
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hz⟩ := h P hP
  exact hr (hle (Module.mem_annihilator.2 hz))

theorem cechLB_acyclic_iff_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Flat f → IsProjBy f → ∀ F : LB Y, F.IsLB → ((∀ P : Ideal R, P.IsMaximal → ∃ (K : Type) (_ : Field K) (χ : R →+* K), RingHom.ker χ = P ∧ ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic)) ∧ ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic) → ∀ (K : Type) [Field K] (χ : R →+* K), ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) := by
  intro R _ _ Y f hf hproj F hF
  have := isProper_of_isProjBy R Y f hproj
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hI : ∀ {κ : Type} {D : κ → Y.Opens}, (∀ i, IsAffineOpen (D i)) → ∀ s : Finset κ,
      s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun hD s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i
  refine ⟨fun H κ _ _ D hD hc p => ?_, fun H K _ χ Y₀ π f₀ h κ _ _ D hD hc p => ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    refine subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_
    obtain ⟨K, _, χ, rfl, HK⟩ := H P hP
    have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
    have hac := HK _ _ _ h' κ
      (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i)
      (fun i => isAffineOpen_preimage_of_isPullback h' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    exact GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre R K χ _ (Fintype.card κ)
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD))
      (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc)
      (fun q => (hac q).of_iso (cechLBBaseChangeIso hF h' (hI hD)).symm) p
  · obtain ⟨L, -, m, s, hc', hs⟩ := hproj
    have hD' : ∀ i, IsAffineOpen (nonzeroLocus (s i)) := fun i => (hs i).1
    have hac := acyclic_extendScalars_of_flat χ _ (Fintype.card (Fin (m + 1)))
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD')) (H _ _ hD' hc')
    have h₁ := (hac p).of_iso (cechLBBaseChangeIso hF h (hI hD'))
    have : IsSeparated f₀ := MorphismProperty.of_isPullback (P := @IsSeparated) h inferInstance
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers K Y₀ f₀ (F.pull π) κ D _
      (fun i => π ⁻¹ᵁ nonzeroLocus (s i)) (LB.isLB_pull hF π) inferInstance hD hc
      (fun i => isAffineOpen_preimage_of_isPullback h (hD' i))
      (by rw [← Scheme.Hom.preimage_iSup, hc']; rfl) p
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e.subsingleton

end GlobalTheory.AbLaw
