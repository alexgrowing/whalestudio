import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap

set_option autoImplicit false

noncomputable section

open Formalism.L2.DIV NumberField
open scoped TensorProduct

namespace GlobalTheory.BaseCmp

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isOfFinOrder_hom_of_finite {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : IsOfFinOrder (f g) :=
  f.isOfFinOrder (isOfFinOrder_of_finite g)

theorem levFn_isOfFinOrder (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E ℂ n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : IsOfFinOrder (levFn β L x) := by
  classical
  have hPP : ∀ PP : Pl E, Finite (kP PP) := fun PP =>
    Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hU : ∀ PP : Pl E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  have hG : ∀ (PP : Pl E) (r : ℕ), Finite (GL (Fin r) (kP PP)) := fun PP r => Finite.of_injective _ Units.val_injective
  have hG0 : Finite (G0 L.Pg L.r) := Pi.finite
  rw [← CommGroup.mem_torsion]
  unfold levFn
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · rw [CommGroup.mem_torsion]
    unfold ext1
    split_ifs with h
    · exact isOfFinOrder_hom_of_finite L.P.chi _
    · exact IsOfFinOrder.one
  · refine Subgroup.prod_mem _ fun PP _ => Subgroup.prod_mem _ fun c _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
  · refine Subgroup.prod_mem _ fun PP _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
end

set_option maxHeartbeats 1600000 in
theorem levLamRoot : LevLamRoot := by
  intro D S T B t k
  have h : IsOfFinOrder (B.levLam t k) := by
    rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
    exact levFn_isOfFinOrder _ _ _
  obtain ⟨m, hm, hmo⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  exact ⟨m, hm.ne', by rw [← Units.val_pow_eq_pow_val, hmo, Units.val_one]⟩

end GlobalTheory.BaseCmp

end
