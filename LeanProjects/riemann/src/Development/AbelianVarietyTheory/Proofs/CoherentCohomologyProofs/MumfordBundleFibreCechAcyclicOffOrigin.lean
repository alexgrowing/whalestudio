import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TranslateDivAdditive
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechComplexAcyclicAdditiveLineBundleNoSectionsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SectionsTranslationDifferenceEqZeroStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.MumfordFibre

theorem lbIso_pull_translDiff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over S} (p : T ⟶ A ⊗ A) (x : 𝟙_ (Over S) ⟶ A) (h : p ≫ fst A A = toUnit T ≫ x) :
    Geo.Tor.LBIso
      ((LB.LinComb L (K := Fin 2) ![(lift (toUnit A ≫ x) (𝟙 A) ≫ μ[A]).left, 𝟙 A.left] ![1, -1]).pull
        (p ≫ snd A A).left)
      ((translDiff A L (𝟙 A)).pull p.left) := by
  have h₁ : (translDiff A L (𝟙 A)).IsLB := LB.isLB_linComb hL _ _
  have h₂ := LB.isLB_linComb hL (K := Fin 2)
    ![(lift (toUnit A ≫ x) (𝟙 A) ≫ μ[A]).left, 𝟙 A.left] ![1, -1]
  refine (CechPic.cls_eq_iff (LB.isLB_pull h₂ _) (LB.isLB_pull h₁ _)).1 ?_
  rw [CechPic.cls_pull h₂, CechPic.cls_pull h₁, CechPic.cls_linComb hL _ _ h₂,
    show CechPic.cls _ h₁ = _ from CechPic.cls_linComb hL _ _ h₁, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul, ← CechPic.pull_comp, ← CechPic.pull_comp]
  congr 3
  fin_cases k
  · show ((p ≫ snd A A) ≫ lift (toUnit A ≫ x) (𝟙 A) ≫ μ[A]).left =
      (p ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left
    rw [comp_lift_assoc, comp_lift_assoc, Category.comp_id, Category.comp_id, h, ← Category.assoc,
      comp_toUnit]
  · exact Category.comp_id _

theorem fibre_acyclic : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (t : Spec (CommRingCat.of K) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of K)), IsPullback π f (fst P.A P.A).left t → t ≫ P.A.hom = 𝟙 _ → t ≠ η[P.A].left → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).Acyclic := by
  intro K _ _ P t Y π f hπ ht hne κ _ _ D hD hcov
  have hpb := ((GlobalTheory.AbProj.abelian_projective_baseChange K P).2 K t Y π f hπ).2.2.2.2.2
  rw [ht] at hpb
  let x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A := Over.homMk t ht
  have hx : x ≠ η[P.A] := fun h => hne (congrArg (·.left) h)
  have hw : π ≫ (P.A ⊗ P.A).hom = f := by
    rw [← Over.w (fst P.A P.A), ← Category.assoc, hπ.w, Category.assoc, ht, Category.comp_id]
  let p : Over.mk f ⟶ P.A ⊗ P.A := Over.homMk π hw
  have hp : p ≫ fst P.A P.A = toUnit _ ≫ x := by
    ext1
    exact hπ.w
  obtain ⟨w, hwg⟩ := lbIso_pull_translDiff P.isLB p x hp
  let e : Y ⟶ P.A.left := π ≫ (snd P.A P.A).left
  have : IsIso e := hpb.isIso_fst_of_isIso
  have he : e ≫ P.A.hom = f := hpb.w.trans (Category.comp_id _)
  have hM := LB.isLB_linComb P.isLB (K := Fin 2)
    ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]
  have hac := GlobalTheory.T.cechComplex_acyclic_additiveLineBundle_noSections K P _ hM (GlobalTheory.TranslateAdditive.translate_div_additive K P x)
    (GlobalTheory.T.sections_translationDifference_eq_zero K P x hx) κ (fun i => inv e ⁻¹ᵁ D i) (fun i => (hD i).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
  obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion K _ P.A.hom _ Y e κ (fun i => inv e ⁻¹ᵁ D i) hM
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hD' : (fun i => e ⁻¹ᵁ inv e ⁻¹ᵁ D i) = D := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  rw [he, hD'] at i₁
  have i₂ := cechLBCongr f D (LB.isLB_pull hM e)
    (LB.isLB_pull (L := translDiff P.A P.L (𝟙 P.A)) (LB.isLB_linComb P.isLB _ _) π) w hwg
  exact fun n => (hac n).of_iso (i₁.symm ≪≫ i₂)

end GlobalTheory.MumfordFibre
