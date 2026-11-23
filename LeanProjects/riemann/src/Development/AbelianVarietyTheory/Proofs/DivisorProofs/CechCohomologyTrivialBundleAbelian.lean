import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.FDim

theorem fromSpecStalk_comp_spec {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isClosed_origin (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (p : Sp K) :
    IsClosed ({(η[A]).left.base p} : Set A.left) := by
  have hr : Set.range (η[A]).left.base = {(η[A]).left.base p} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hs : Subsingleton (Sp K) := inferInstance
      obtain rfl : q = p := hs.elim q p
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rw [← hr]
  exact (η[A]).left.isClosedEmbedding.isClosed_range

theorem cechLB_triv_finrank_one_two : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  intro K _ _ A _ g hA hsm κ _ _ D hD hcov
  obtain ⟨L, H, _, j, hL, hproj, hgen, hj, hci, hfin, hK⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hx₀ : (η[A]).left.base p ∈ Set.range (η[A]).left.base := ⟨p, rfl⟩
  obtain ⟨J, C, φ, hJ, hφ, hfree, hbdd, hcok, hfib, hiso⟩ :=
    GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin K A g hA hsm L H j hL hproj hgen hj hci hfin hK _ hx₀
  obtain ⟨f, hf⟩ := GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements K A g hA hsm H j hj hci hfin _ hx₀ J hJ
  obtain ⟨hJt, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin _ hx₀ J hJ
  subst hf
  let σ : K →+* A.left.presheaf.stalk ((η[A]).left.base p) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.hom.appTop ≫
      A.left.presheaf.germ ⊤ ((η[A]).left.base p) trivial).hom
  have hσ : A.left.fromSpecStalk ((η[A]).left.base p) ≫ A.hom = Spec.map (CommRingCat.ofHom σ) := by
    rw [fromSpecStalk_comp_spec]
    rfl
  have hloc : IsLocalHom σ := ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩
  obtain ⟨-, -, hreg, hdim⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth K A.left A.hom g hsm _ (isClosed_origin K A p) σ hσ hloc
  have hbot : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot (A.left.presheaf.stalk ((η[A]).left.base p)))
  haveI : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left.base p)) :=
    IsRegularLocalRing.of_ringEquiv e
  have hdim' : ringKrullDim (A.left.presheaf.stalk ((η[A]).left.base p)) = g := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  have hex := GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres _ g hdim' C hfree hbdd hfib
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_homology_one_two_dualResolution _ g hdim' f hJt hart C hfree hex hcok K φ hφ
  haveI := hA.proper
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K A.left A.hom (LB.triv A.left) κ D
      (LB.isLB_triv _) inferInstance hproj hD hcov i
  · obtain ⟨e1⟩ := hiso κ D hD hcov 1
    rw [← e1.finrank_eq]
    exact h1
  · obtain ⟨e2⟩ := hiso κ D hD hcov 2
    rw [← e2.finrank_eq]
    exact h2

end GlobalTheory.AbCoh.FDim
