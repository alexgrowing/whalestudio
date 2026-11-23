import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsCmp

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B]
    (x : 𝟙_ (Over S') ⟶ (Over.pullback f).obj B) (x₀ : 𝟙_ (Over S) ⟶ B)
    (hx : f ≫ x₀.left = x.left ≫ pullback.fst B.hom f) (N : ℕ) (h : x₀ ^ N = 1) : x ^ N = 1 := by
  have e : ∀ k, f ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst B.hom f := fun k =>
    GlobalTheory.ZH.MultInt.pow_left_pullback f B (T := 𝟙_ (Over S')) (T₀ := 𝟙_ (Over S)) f
      (by simp) x x₀ hx k
  have e0 := e 0
  have eN := e N
  rw [h, ← pow_zero x₀, e0] at eN
  rw [← pow_zero x]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact eN.symm
  · exact (Over.w (x ^ N)).trans (Over.w (x ^ 0)).symm

end GlobalTheory.TorsCmp

open GlobalTheory.TorsCmp in

theorem GlobalTheory.TorsCmp.torsion_section_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := by
  intro k₀ K _ _ _ _ B _ hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf N hN y₀ hy₀ c hc₁ hc₂
  haveI := hΨ
  haveI := hf₀
  haveI : IsAbelianScheme ((Over.pullback (spMap (algebraMap k₀ R))).obj B) :=
    GlobalTheory.isAbelianScheme_overPullback _ B hB
  have hgf : spMap g.toRingHom ≫ spMap (algebraMap k₀ R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : g.toRingHom.comp (algebraMap k₀ R) = RingHom.id k₀ := by
      ext r; exact g.commutes r
    rw [this]; exact Spec.map_id _
  have hNR : IsUnit (N : Γ(Sp R, ⊤)) := by
    have h1 : IsUnit (N : k₀) := Ne.isUnit hN
    have h2 : IsUnit (N : R) := by simpa using h1.map (algebraMap k₀ R)
    simpa using h2.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let cc : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk c (by exact hc₂)
  let bb : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk (pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left) (𝟙 _) (by
      rw [Category.assoc, Category.assoc, Over.w f₀, Over.w y₀, Category.id_comp]; rfl))
      (pullback.lift_snd _ _ _)
  have hcc : cc ^ N = 1 := pow_eq_one_of_pullback _ B cc y₀ hc₁.symm N hy₀
  have ha : (cc ≫ Ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hcc, MonObj.one_comp]
  have hb : bb ^ N = 1 := by
    refine pow_eq_one_of_pullback _ B bb (y₀ ≫ f₀) (pullback.lift_fst _ _ _).symm N ?_
    rw [← MonObj.pow_comp, hy₀, MonObj.one_comp]
  have hxc : spMap g.toRingHom ≫ c = y₀.left ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc₁, reassoc_of% hgf, Category.assoc, hσ₁, Category.comp_id]
    · rw [Category.assoc, hc₂, Category.assoc, hσ₂, ← Category.assoc, Over.w y₀]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hpt : spMap g.toRingHom ≫ (cc ≫ Ψ).left = spMap g.toRingHom ≫ bb.left := by
    apply pullback.hom_ext
    · change spMap g.toRingHom ≫ c ≫ Ψ.left ≫ _ = spMap g.toRingHom ≫ pullback.lift _ _ _ ≫ _
      rw [reassoc_of% hxc, ← hf, pullback.lift_fst, reassoc_of% hgf]
    · rw [Category.assoc, Category.assoc]
      exact congrArg _ ((Over.w (cc ≫ Ψ)).trans (Over.w bb).symm)
  have hab := GlobalTheory.HkFam.ListedSubgroup.section_eq _ hNR ha hb (spMap g.toRingHom) hpt
  have := congrArg (fun z => z.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ R))) hab
  simp only [cc, bb, Over.comp_left, Over.homMk_left, Category.assoc] at this
  rw [this, pullback.lift_fst]
