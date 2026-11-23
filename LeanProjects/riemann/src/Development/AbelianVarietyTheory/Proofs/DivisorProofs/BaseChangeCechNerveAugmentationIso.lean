import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) := by
  have : PreservesLimit (cospan f g) sch := by
    unfold sch; infer_instance
  exact h.map sch

theorem bc_cechAug_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S),
    ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U)
      (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U),
      e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  intro S W V r f U
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst f (pullback.fst r U.hom))
    (pullback.snd f (pullback.fst r U.hom)) f (pullback.fst r U.hom) (IsPullback.of_hasPullback _ _)
  have hQ := sch_isPullback (IsPullback.of_hasPullback r U.hom)
  have hP := hm.paste_vert hQ
  refine ⟨hP.isoPullback, hQ.isoPullback, ?_⟩
  apply pullback.hom_ext
  · simp only [bc, bcMap, Category.assoc, pullback.lift_fst, pullback.map]
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]
    exact hm.w
  · simp only [bc, bcMap, Category.assoc, pullback.lift_snd, pullback.map, Category.comp_id]
    rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]

end GlobalTheory.EtC
