import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsIsoAppOfIsAbelianScheme

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem locus_of_locally : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  intro S A Y _ hA N hN h0 T t hloc
  let T₀ : Over S := Over.mk (t ≫ Y.hom)
  let y : T₀ ⟶ Y := Over.homMk t rfl
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ y)
  have hM : M.IsLB := pull_isLB hN _
  have key : ∀ (Z : Over S) (u : Z ⟶ A ⊗ T₀), evc hN (u ≫ fst A T₀) (u ≫ snd A T₀ ≫ y) = 0 →
      Triv (M.pull u.left) := by
    intro Z u h
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM]
    have e := pull_evc hN u (fst A T₀) (snd A T₀ ≫ y)
    rw [h] at e
    exact e
  show Triv M
  refine GlobalTheory.CompanionTheory.Ar.Approx.triv_of_section_of_locally_triv (A ⊗ T₀).left T (snd A T₀).left
    (lift (1 : T₀ ⟶ A) (𝟙 T₀)).left ?_ ?_ M hM ?_ ?_
  · rw [← Over.comp_left, lift_snd]; rfl
  · intro U
    exact GlobalTheory.CompanionTheory.Ar.Approx.isIso_app_of_isAbelianScheme T ((Over.pullback T₀.hom).obj A)
      (CubeGen.isAb_baseChange hA T₀.hom) U
  · refine key T₀ _ ?_
    rw [lift_fst, lift_snd_assoc, Category.id_comp]
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  · intro x
    obtain ⟨W, hx, hW⟩ := hloc x
    refine ⟨W, hx, ?_⟩
    let p := (snd A T₀).left
    let W₀ : Over S := Over.mk ((W.ι ≫ t) ≫ Y.hom)
    let y' : W₀ ⟶ Y := Over.homMk (W.ι ≫ t) rfl
    let Z : Over S := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom)
    let u : Z ⟶ A ⊗ T₀ := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let l : Z.left ⟶ W₀.left := IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr
    have hl : l ≫ W.ι = (p ⁻¹ᵁ W).ι ≫ p := IsOpenImmersion.lift_fac _ _ _
    have wz : l ≫ W₀.hom = Z.hom := by
      have hs : p ≫ t ≫ Y.hom = (A ⊗ T₀).hom := Over.w (snd A T₀)
      show l ≫ (W.ι ≫ t) ≫ Y.hom = (p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom
      rw [← hs, ← Category.assoc (p ⁻¹ᵁ W).ι, ← hl]
      simp only [Category.assoc]
    let w : Z ⟶ W₀ := Over.homMk l wz
    have hwy : w ≫ y' = u ≫ snd A T₀ ≫ y := by
      apply Over.OverMorphism.ext
      show l ≫ W.ι ≫ t = (p ⁻¹ᵁ W).ι ≫ p ≫ t
      rw [← Category.assoc, hl, Category.assoc]
    refine key Z u ?_
    have e := pull_evc hN (lift (u ≫ fst A T₀) w) (fst A W₀) (snd A W₀ ≫ y')
    rw [(triv_ev_iff hN _ _).1 hW, map_zero, lift_fst, lift_snd_assoc, hwy] at e
    exact e.symm

end GlobalTheory.CompanionTheory.TrivLoc
