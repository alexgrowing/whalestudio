import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

open TensorProduct in

theorem _root_.GlobalTheory.BSP.semiBC_iff_isBaseChange (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type)
    [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N)
    (h : ∀ x, u' x = u x) : _root_.GlobalTheory.Prism.SemiBC u ↔ IsBaseChange B u' := by
  constructor
  · intro hu
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
    let v : M →ₛₗ[algebraMap A B] Q :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun a x => by simp [algebraMap_smul] }
    obtain ⟨w, hw, hw'⟩ := hu Q v
    refine ⟨w, ?_, fun w₂ hw₂ => hw' w₂ fun x => ?_⟩
    · ext x
      simp [h, hw x, v]
    · rw [← h]
      exact LinearMap.congr_fun hw₂ x
  · intro hb Q _ _ v
    letI : Module A Q := Module.compHom Q (algebraMap A B)
    haveI : IsScalarTower A B Q :=
      ⟨fun a b q => by
        show (a • b) • q = algebraMap A B a • b • q
        rw [Algebra.smul_def, mul_smul]⟩
    let g : M →ₗ[A] Q :=
      { toFun := v
        map_add' := v.map_add
        map_smul' := fun a x => by
          rw [v.map_smulₛₗ]
          rfl }
    refine ⟨hb.lift g, fun x => ?_, fun w hw => hb.algHom_ext _ _ fun x => ?_⟩
    · rw [← h, hb.lift_eq]
      rfl
    · rw [hb.lift_eq, h, hw]
      rfl

end GlobalTheory.BSP
