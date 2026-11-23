import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismAlgebraisingThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

open GlobalTheory.EndData GlobalTheory.AbLaw in

theorem exists_hom_of_levels {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R}
    (hC : IsAdicComplete I R) (Y Z : Over (Spec (CommRingCat.of R))) (sY : Smooth Y.hom) (sZ : Smooth Z.hom)
    (pY : IsProjBy Y.hom) (pZ : IsProjBy Z.hom) (s : Y ⟶ Z) (f : ∀ e, (thickObj R I e Y).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e) :
    ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  have w₁ : (fst Y Z).left ≫ Y.hom = (Y ⊗ Z).hom := Over.w _
  have w₂ : (snd Y Z).left ≫ Z.hom = (Y ⊗ Z).hom := Over.w _
  have sm : Smooth (Y ⊗ Z).hom := by
    show Smooth (pullback.fst Y.hom Z.hom ≫ Y.hom)
    infer_instance
  let p : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ (thickObj R I e Y).left := fun e =>
    ((Over.pullback (thick R I e)).map (fst Y Z)).left
  have hp : ∀ e, p e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst (Y ⊗ Z).hom (thick R I e) ≫ (fst Y Z).left :=
    fun e => map_fst e _
  let F : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ pullback Y.hom Z.hom := fun e =>
    pullback.lift (p e ≫ pullback.fst Y.hom (thick R I e)) (p e ≫ f e) (by
      rw [Category.assoc, Category.assoc, hf])
  have F₁ : ∀ e, F e ≫ pullback.fst _ _ = p e ≫ pullback.fst Y.hom (thick R I e) := fun e => pullback.lift_fst _ _ _
  have F₂ : ∀ e, F e ≫ pullback.snd _ _ = p e ≫ f e := fun e => pullback.lift_snd _ _ _
  have tp : ∀ e, thickMap R I e (Y ⊗ Z) ≫ p (e + 1) = p e ≫ thickMap R I e Y := fun e => trans_map e _
  obtain ⟨g, hg⟩ := EndAlg.exists_end_of_thickenings R I hC (Y ⊗ Z) sm (isProjBy_tensor R Y Z pY pZ) F
    (fun e => by
      show F e ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = _
      rw [← Category.assoc, F₁, hp, Category.assoc, w₁])
    (fun e => by
      show (thickMap R I e (Y ⊗ Z) ≫ F (e + 1) : _ ⟶ pullback Y.hom Z.hom) = F e
      apply pullback.hom_ext
      · rw [Category.assoc, F₁, F₁, ← Category.assoc, tp, Category.assoc, trans_fst]
      · rw [Category.assoc, F₂, F₂, ← Category.assoc, tp, Category.assoc, hc])
  refine ⟨lift (𝟙 Y) s ≫ g ≫ snd Y Z, fun e => ?_⟩
  have hj : ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s)).left ≫ p e = 𝟙 _ := by
    show ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s) ≫ (Over.pullback (thick R I e)).map (fst Y Z)).left = _
    rw [← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
    rfl
  have k : F e ≫ (snd Y Z).left = p e ≫ f e := F₂ e
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← map_fst, Category.assoc,
    ← Category.assoc (pullback.fst _ _), hg]
  erw [k]
  rw [← Category.assoc]
  erw [hj]
  exact Category.id_comp _

open GlobalTheory.EndTorus in

theorem exists_abelian_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D₁ D₂ : DegPre R} {e : ℕ} {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ b : thickObj R I e D₁.P.A ⟶ thickObj R I e D₂.P.A, IsMonHom b ∧ g₁.q ≫ b = a ≫ g₂.q := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := g₁.q_hom
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  exact FlatQuotient.exists_desc g₁.q g₁.i (a ≫ g₂.q) g₁.isKernel h1

open GlobalTheory.EndData in

theorem exists_abelian_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => exists_abelian_level hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  have hql : ∀ e, (U₁.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).q.left :=
    fun e => congrArg (·.left) (hq e)
  obtain ⟨aB, haB⟩ := exists_hom_of_levels hC D₁.toPre.P.A D₂.toPre.P.A D₁.toPre.P.isAb.smooth
    D₂.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _))
    (AbProj.isProjBy_of_isPullback D₂.toPre.P (IsPullback.id_horiz _)) 1
    (fun e => (b e).left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D₂.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, pullback.condition])
    (fun e => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      have : Epi (U₁.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U₁.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U₁.gt (e + 1)).q.left, hql, ← Category.assoc (U₁.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G₂), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D₂.toPre.P.isAb
    D₁.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact (hq e).symm

end GlobalTheory.Mum.Two
