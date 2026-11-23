import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplex
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem exists_free_complex_of_primitive_cech : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (K : Type) [Field K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K] (cechLB f' (F.pull π) D).homology i) := by
  intro A _ _ _ B _ _ hB hP g hg F hF hu P
  obtain ⟨u, hu⟩ := hu
  have := hB.smooth
  have := hB.proper
  obtain ⟨H, hH, m, s, hs⟩ := id hP
  have hD := (VeryAmpleCharts.compact_quasiSeparated_isAffineOpen A _ B.hom H m s hH hs).2.2
  have hD₁ := fun i => (hs.2 i).1
  obtain ⟨C, ψ, h0, hfin, -, hproj, -, -, hq⟩ := exists_finite_projective_complex_quasiIso.{0, 0}
    (cechLB B.hom F fun i => nonzeroLocus (s i)) (Fintype.card (Fin (m + 1)))
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X B.hom hF hD)
    (cechLB_homology_finite_of_affine_cover A _ B.hom F _ _ hF inferInstance hP hD₁ hs.1)
  have hC : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i) := fun i => by
    have := hfin i
    have := hproj i
    exact ⟨Module.free_of_flat_of_isLocalRing, hfin i⟩
  refine ⟨C, hC, ⟨_, h0⟩, SecKernel.nonempty_equiv_of_model ψ hF hs.1 hD hq hC P, ?_, ?_⟩
  · intro K _ _ φ X' π f' hX i hi
    let t := Spec.map (CommRingCat.ofHom φ)
    let B' := (Over.pullback t).obj B
    have : IsCommMonObj B' := Functor.isCommMonObj_obj
    have hB' : IsAbelianScheme B' := Out.TLinPf.isAb_pullback t B hB
    have sq : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
    have hP' : IsProjBy B'.hom := isProjBy_baseChange _ _ φ _ _ _ _ _ sq hP
    have hF' := LB.isLB_pull hF (pullback.fst B.hom t)
    have ha := fun j => isAffineOpen_preimage_of_isPullback sq (hD₁ j)
    have hc := PerfOfModel.iSup_preimage (pullback.fst B.hom t) hs.1
    have hq' : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ) :=
      letI := φ.toAlgebra
      hq K
    refine (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ ≫ (cechLBBaseChangeIso hF sq hD).hom) i).2 ?_
    rcases hi with hi | hi
    · have := isIntegral_left_of_isAbelianScheme_field B' hB'
      have := hB'.proper
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n := g)
      exact cechLB_exactAt_of_dim_lt K B'.left B'.hom g _
        (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) sq hg) hP' inferInstance hF' _ _ ha hc i hi
    · obtain ⟨U, ⟨c⟩⟩ := GtBaseChange.exists_lamChart t B F
      exact GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed K B' hB' hP' _ hF' ⟨_, GtBaseChange.genPull_isGen c hu⟩
        (fun h => hi (CubeOpen.triv_comp (hX.isoIsPullback _ _ sq).hom (hX.isoIsPullback_hom_fst _ _ sq) h))
        _ _ ha hc i
  · intro K _ φ X' π f' hX κ _ _ D hDa hDc i
    have hq' : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ) :=
      letI := φ.toAlgebra
      hq K
    let χ := ((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ ≫ (cechLBBaseChangeIso hF hX hD).hom
    have : QuasiIso χ := inferInstance
    have e₁ := (isoOfQuasiIsoAt χ i).toLinearEquiv
    have : IsSeparated f' := MorphismProperty.of_isPullback (P := @IsSeparated) hX inferInstance
    obtain ⟨e₂⟩ := cechLB_homology_equiv_of_affine_covers K X' f' (F.pull π) (Fin (m + 1))
      (fun j => π ⁻¹ᵁ nonzeroLocus (s j)) κ D (LB.isLB_pull hF π) inferInstance
      (fun j => isAffineOpen_preimage_of_isPullback hX (hD₁ j))
      (PerfOfModel.iSup_preimage π hs.1) hDa hDc i
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.AbLaw
