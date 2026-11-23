import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
import Development.EtaleCohomology.EtaleSheaves.LeafObjGluePf
import Development.EtaleCohomology.EtaleSheaves.LeafInclDescendPf
import Development.EtaleCohomology.EtaleSheaves.DgMapIsPullback
import Development.EtaleCohomology.EtaleSheaves.LeafPairRelPf
import Development.EtaleCohomology.EtaleSheaves.LeafTripleFPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.DiagramDescent

theorem descendFP_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) : LeafDescendFP := by
  have hO : LeafObjFP := LateralTheory.E.LeafObjFPPf.objectDescent_of_affineDescent hA
    (LateralTheory.E.LeafObjGluePf.LeafObjGlue_of (LateralTheory.E.LeafInclDescendPf.LeafInclDescend_of hI) hG) hQ
  exact diagramDescent_of_objects_pairs_triples hO (LateralTheory.E.LeafPairFPPf.pairDescent_of_objects_morphisms hO (LateralTheory.E.LeafMapFPPf2.morphismDescent_of_isLimit hL))
    (LateralTheory.E.LeafTripleFPPf.tripleDescent_of_pairRelation (LateralTheory.E.LeafPairRelPf.LeafPairRel_of hO hF))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem cond {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h.w

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h

theorem LeafDescendPreMap_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) :
    LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hRfg, D0, D1, D2, q, d1, d2, v0, v1, v2, hpre⟩ :=
    descendFP_of hA hG hQ hI hL hF k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨hq0, hq1, hq2, p0, p1, p2, m1, m2⟩ := hpre
  have : LocallyOfFinitePresentation p := LateralTheory.E.LeafDescendMapPf.lfp p
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hlfp : LocallyOfFinitePresentation (pullback.snd p bk) := inferInstance
  have ha : e ≫ p = (c0 ≫ toR R) ≫ bk := by
    rw [he, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_base]
  obtain ⟨R', h, hR'fg, g, hg1, hg2⟩ := hF k Ω R hRfg c0 q v0 hq0 p0 (pullback.snd p bk) hlfp
    (pullback.lift e (c0 ≫ toR R) ha) (pullback.lift_snd _ _ _)
  let e1 : pullback (d1 ≫ q) (incl h) ⟶ pullback q (incl h) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl h) ⟶ pullback (d1 ≫ q) (incl h) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl h) = pullback.snd (d2 ≫ d1 ≫ q) (incl h) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR'fg, _, _, _, pullback.snd q (incl h), e1, e2, g ≫ pullback.fst p bk,
    pullback.lift v0 (c0 ≫ toR R') (cond h p0), pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond h p1),
    pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond h p2), ?_, ⟨fp_snd _ _ hq0, ?_, ?_, sq h p0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc,
      LateralTheory.E.LeafDescendMapPf.incl_base]
  · rw [E1]; exact fp_snd _ _ hq1
  · rw [E2]; exact fp_snd _ _ hq2
  · rw [E1]; exact sq h p1
  · rw [E2]; exact sq h p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [← Category.assoc, hg2, pullback.lift_fst]

end LateralTheory.E.DiagramDescent

end
