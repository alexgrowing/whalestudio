import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
open scoped Matrix
open Filter Topology

namespace GlobalTheory

theorem banach_oneParamGroup_eq_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hm : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t, NormedSpace.exp (t • X) = M t := by
  first
  | exact @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | (apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq ..)

theorem matrix_oneParamGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := banach_oneParamGroup_eq_exp M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩

end GlobalTheory
