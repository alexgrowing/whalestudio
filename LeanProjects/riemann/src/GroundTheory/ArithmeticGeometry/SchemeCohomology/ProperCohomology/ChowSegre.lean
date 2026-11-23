import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AppLEFromOfGlobalSectionsChartHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A]

def multiProjDim : (k : ℕ) → (Fin (k + 1) → ℕ) → ℕ
  | 0, n => n 0
  | k + 1, n => n 0 * multiProjDim k (Fin.tail n) + n 0 + multiProjDim k (Fin.tail n)

def multiProjEmbOverBase : (k : ℕ) → (n : Fin (k + 1) → ℕ) →
    {e : MP A k n ⟶ projectiveSpace A (multiProjDim k n) //
      e ≫ toSpecBase A (multiProjDim k n) = mpStr A k n}
  | 0, _ => ⟨𝟙 _, Category.id_comp _⟩
  | k + 1, n =>
    let e' := multiProjEmbOverBase k (Fin.tail n)
    ⟨pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
        (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) e'.1 (𝟙 _) (by simp) (by simp [e'.2]) ≫
      segre A (n 0) (multiProjDim k (Fin.tail n)), by
      change (_ ≫ segre A (n 0) (multiProjDim k (Fin.tail n))) ≫ toSpecBase A
          (n 0 * multiProjDim k (Fin.tail n) + n 0 + multiProjDim k (Fin.tail n)) =
        pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ toSpecBase A (n 0)
      rw [Category.assoc, segre_toSpecBase, pullback.lift_fst_assoc, Category.comp_id]⟩

def multiProjEmb (k : ℕ) (n : Fin (k + 1) → ℕ) :
    MP A k n ⟶ projectiveSpace A (multiProjDim k n) :=
  (multiProjEmbOverBase A k n).1

@[reassoc (attr := simp)]
lemma multiProjEmb_toSpecBase (k : ℕ) (n : Fin (k + 1) → ℕ) :
    multiProjEmb A k n ≫ toSpecBase A (multiProjDim k n) = mpStr A k n :=
  (multiProjEmbOverBase A k n).2

instance isClosedImmersion_multiProjEmb :
    (k : ℕ) → (n : Fin (k + 1) → ℕ) → IsClosedImmersion (multiProjEmb A k n)
  | 0, _ => by
    change IsClosedImmersion (𝟙 _)
    infer_instance
  | k + 1, n => by
    have ih := isClosedImmersion_multiProjEmb k (Fin.tail n)
    have hpb : IsPullback
        (pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
          (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) (multiProjEmb A k (Fin.tail n)) (𝟙 _)
          (by simp) (by rw [Category.comp_id, multiProjEmb_toSpecBase]))
        (pullback.snd _ _) (pullback.snd _ _) (multiProjEmb A k (Fin.tail n)) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
      have h1 : pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
          (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) (multiProjEmb A k (Fin.tail n))
          (𝟙 _) (by simp) (by rw [Category.comp_id, multiProjEmb_toSpecBase]) ≫ pullback.fst _ _ =
          pullback.fst _ _ := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      rw [h1, multiProjEmb_toSpecBase]
      exact IsPullback.of_hasPullback _ _
    have : IsClosedImmersion (pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n))
        (toSpecBase A (n 0)) (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _)
        (multiProjEmb A k (Fin.tail n)) (𝟙 _) (by simp)
        (by rw [Category.comp_id, multiProjEmb_toSpecBase])) :=
      MorphismProperty.of_isPullback hpb.flip ih
    exact @IsClosedImmersion.comp _ _ _ _ (segre A (n 0) (multiProjDim k (Fin.tail n))) this
      inferInstance

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
