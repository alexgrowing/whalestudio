import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem fibAc_of_closed_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  intro k _ _ X T Z a b p q H ha _ _ G hG R _ t _ Y π f Hy hfib κ _ _ D hD hc n
  have HP := Hy.paste_horiz H
  have hproj : IsProjBy f := by
    obtain ⟨c, hcb⟩ := Spec.map_surjective (t ≫ b)
    have HP' : IsPullback (π ≫ p) f a (spMap c.hom) := by
      have : spMap c.hom = t ≫ b := by
        rw [← hcb]; rfl
      rw [this]; exact HP
    exact (ProjSpace.isProjBy_iff_isProjOver f).2
      (ProjSpace.isProjOver_of_isPullback_spMap c.hom HP'
        ((ProjSpace.isProjBy_iff_isProjOver a).1 ha))
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) HP inferInstance
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) HP inferInstance
  haveI hN : IsNoetherianRing R := by
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
      LocallyOfFiniteType.isLocallyNoetherian (t ≫ b)
    exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have hflat : ∀ p, Module.Flat R ((cechLB f (G.pull π) D).X p) := flat_cechLB_X f hM hI
  have hfin := GlobalTheory.T.finite_cechLB_homology_of_affine_cover R Y f _ κ D hM inferInstance hproj hD hc
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine GlobalTheory.MumfordAway.subsingleton_of_points k R (t ≫ b) _ fun χ hχ => ?_
  refine exists_smul_homology_eq_zero_of_acyclic_fibre R k χ _ (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) hflat hfin ?_ n
  have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have P1 := h'.paste_horiz HP
  rw [hχ] at P1
  let u := pullback.fst f (Spec.map (CommRingCat.ofHom χ))
  let v := pullback.snd f (Spec.map (CommRingCat.ofHom χ))
  let e := u ≫ π ≫ p
  haveI : IsIso e := P1.isIso_fst_of_isIso
  have he : e ≫ a = v := P1.w.trans (Category.comp_id _)
  let σ : X ⟶ Z := inv e ≫ u ≫ π
  have hσp : σ ≫ p = 𝟙 X := by
    simp only [σ, Category.assoc]
    exact IsIso.inv_hom_id e
  have hes : e ≫ σ = u ≫ π := by simp [σ]
  have hσq : σ ≫ q = a ≫ Spec.map (CommRingCat.ofHom χ) ≫ t := by
    rw [← cancel_epi e, ← Category.assoc e σ, hes, ← Category.assoc e a, he, Category.assoc u, Hy.w]
    exact (reassoc_of% h'.w) t
  have hac := hfib (Spec.map (CommRingCat.ofHom χ)) σ hχ hσp hσq κ (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i)
    (fun i => (isAffineOpen_preimage_of_isPullback h' (hD i)).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]; rfl)
  obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) _ e κ
    (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i) (LB.isLB_pull hG σ)
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hD' : (fun i => e ⁻¹ᵁ inv e ⁻¹ᵁ u ⁻¹ᵁ D i) = fun i => u ⁻¹ᵁ D i := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  rw [he, hD'] at i₁
  obtain ⟨w₁, hw₁⟩ : ∃ w : LB.Iso ((G.pull σ).pull e) (G.pull (u ≫ π)), w.IsGen :=
    hes ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ e
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π u
  have hL₁ : ((G.pull σ).pull e).IsLB := LB.isLB_pull (LB.isLB_pull hG σ) e
  have hL₂ : ((G.pull π).pull u).IsLB := LB.isLB_pull hM u
  have hL₃ : (G.pull (u ≫ π)).IsLB := LB.isLB_pull hG _
  have c₁ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₁ hL₃ w₁ hw₁
  have c₂ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₂ hL₃ w₂ hw₂
  have E := cechLBBaseChangeIso hM h' hI ≪≫ c₂ ≪≫ c₁.symm ≪≫ i₁
  exact fun m => (hac m).of_iso E.symm

end GlobalTheory.CompanionTheory.PointSurjectivity
