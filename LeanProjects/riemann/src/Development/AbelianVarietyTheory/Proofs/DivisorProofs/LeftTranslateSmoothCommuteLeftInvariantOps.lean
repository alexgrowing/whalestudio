import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem isSmoothFun_leftTranslate (h : IsExpLieAlgebra G 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) : h.IsSmoothFun (fun y => f (g * y)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g'
  simpa only [mul_assoc] using hf (g * g')

def leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨fun y => (f : G → ℂ) (g * y), isSmoothFun_leftTranslate h f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G)
    (f : h.smoothFuns (F := ℂ)) (y : G) :
    ((leftTranslateSmoothEnd h g f : h.smoothFuns (F := ℂ)) : G → ℂ) y = (f : G → ℂ) (g * y) :=
  rfl

theorem commute_rightDerivEnd_leftTranslate (h : IsExpLieAlgebra G 𝔤) (g : G) (X : 𝔤) :
    Commute (h.rightDerivEnd (F := ℂ) X) (leftTranslateSmoothEnd h g) := by
  ext f y
  simp only [Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
    coe_leftTranslateSmoothEnd, IsExpLieAlgebra.rightDeriv]
  simp only [mul_assoc]

theorem leftTranslate_smooth_commute (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸)
    (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G) :
    ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧
      ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y,
        (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  refine ⟨leftTranslateSmoothEnd h g f, fun y => rfl, fun T hT y => ?_⟩
  have hc : Commute T (leftTranslateSmoothEnd h g) := by
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT ?_).symm
    rintro _ ⟨X, rfl⟩
    exact (commute_rightDerivEnd_leftTranslate h g X).symm
  have := congrArg (fun S : Module.End ℂ (h.smoothFuns (F := ℂ)) => ((S f : h.smoothFuns (F := ℂ)) : G → ℂ) y) hc.eq
  simpa only [Module.End.mul_apply, coe_leftTranslateSmoothEnd] using this

end GlobalTheory
