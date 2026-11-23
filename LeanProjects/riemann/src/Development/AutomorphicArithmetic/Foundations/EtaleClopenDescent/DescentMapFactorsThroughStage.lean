import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafPairRelPf
import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf

namespace UpperTheory.Cb.DescentMapFactorization

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {E : Scheme.{0}} (p : E ⟶ Sp R)

private def tR : LateralTheory.E.LeafDescendMapPf.D R p ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.snd _ _ ≫ incl S.unop.2.1
  naturality S T h := by
    simp only [Functor.const_obj_map, Category.comp_id]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.incl_incl]
    exact (Category.comp_id _).symm

private lemma tR_app (S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ) : (tR R p).app S =
    pullback.snd p (incl S.unop.2.1) ≫ incl S.unop.2.1 := rfl

end UpperTheory.Cb.DescentMapFactorization

open UpperTheory.Cb.DescentMapFactorization in
theorem UpperTheory.Cb.descent_map_factors_through_stage :
    LateralTheory.E.LeafPairRelPf.LeafFactorStage := by
  intro k _ Ω _ _ R hR C E Y c p w hp hs f hf a ha
  obtain ⟨h1, h2, h3⟩ := hp
  haveI : Nonempty (LateralTheory.E.LeafDescendMapPf.J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, CompactSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p _)
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, QuasiSeparatedSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p _)
  have hcomm : (LateralTheory.E.LeafDescendMapPf.cone R p c w hs).π ≫ tR R p = (Functor.const _).map (a ≫ f) := by
    ext S
    simp only [NatTrans.comp_app, Functor.const_map_app]
    rw [tR_app]
    simp only [pullback.lift_snd_assoc, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]
    exact ha.symm
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (LateralTheory.E.LeafDescendMapPf.D R p) (tR R p) f (LateralTheory.E.LeafDescendMapPf.cone R p c w hs)
    (LateralTheory.E.LeafDescendMapPf.coneIsLimit R p c w hs hR) a hcomm
  exact ⟨S.unop.1, S.unop.2.1, S.unop.2.2, g, hg2, hg1⟩

end
