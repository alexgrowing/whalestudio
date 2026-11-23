import Mathlib

namespace Bl.general_b_fact_upper_alt_form

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] {n k : Type} [Fintype.{0} n] [DecidableEq.{1} n] [inst_3 : Fintype.{0} k]
  [DecidableEq.{1} k] (f : RingHom.{0, 0} K Complex) (A : Matrix.{0, 0, 0} n k K),
  Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} A) →
    Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} A (DFunLike.coe.{1, 1, 1} f))) := by
  intro K _ n k _ _ _ _ f A hA
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun x y hxy => hA (by simpa only [Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
  have h1 : (LinearMap.toMatrix' g).map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]
  intro v w hvw
  have h2 := congrArg (fun u => Matrix.mulVec ((LinearMap.toMatrix' g).map f) u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using h2

end Bl.general_b_fact_upper_alt_form
