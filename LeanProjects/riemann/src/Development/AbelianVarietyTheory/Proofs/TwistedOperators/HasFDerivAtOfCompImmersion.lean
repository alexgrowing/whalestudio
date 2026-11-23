import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasFDerivAt_of_comp_immersion : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (Φ : E → F) (ψ : E → E) (x : E) (A D : E →L[ℝ] F), HasStrictFDerivAt Φ A (ψ x) → Function.Injective A → ContinuousAt ψ x → HasFDerivAt (fun y => Φ (ψ y)) D x → ∃ P : E →L[ℝ] E, HasFDerivAt ψ P x ∧ A.comp P = D := by
  intro E F _ _ _ _ _ _ Φ ψ x A D hA hinj hψ hD

  obtain ⟨g, hg⟩ := (A : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let L : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hLA : ∀ v, L (A v) = v := fun v => by
    have h := LinearMap.congr_fun hg v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe] at h
    first
      | exact h
      | simpa [L] using h
      | (rw [show (L : F → E) = g from LinearMap.coe_toContinuousLinearMap' g]; exact h)

  have hr : (fun y => Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) =o[nhds x] (fun y => ψ y - ψ x) :=
    hA.hasFDerivAt.isLittleO.comp_tendsto hψ
  have hs : (fun y => Φ (ψ y) - Φ (ψ x) - D (y - x)) =o[nhds x] (fun y => y - x) :=
    hD.isLittleO
  have hLr : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x))) =o[nhds x] (fun y => ψ y - ψ x) :=
    (L.isBigO_comp _ _).trans_isLittleO hr

  have hu : (fun y => ψ y - ψ x) =O[nhds x] (fun y => y - x) := by
    have h1 := hLr.right_isBigO_add
    have hsum : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) + (ψ y - ψ x))
        = fun y => L (Φ (ψ y) - Φ (ψ x)) := by
      funext y
      simp only [map_sub, hLA]
      abel
    rw [hsum] at h1
    exact h1.trans ((L.isBigO_comp _ _).trans hD.isBigO_sub)

  have hP : HasFDerivAt ψ (L.comp D) x := by
    rw [hasFDerivAt_iff_isLittleO]
    have hdiff : (fun y => L (Φ (ψ y) - Φ (ψ x) - D (y - x)) - L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)))
        = fun y => ψ y - ψ x - (L.comp D) (y - x) := by
      funext y
      simp only [map_sub, hLA, ContinuousLinearMap.comp_apply]
      abel
    rw [← hdiff]
    exact ((L.isBigO_comp _ _).trans_isLittleO hs).sub (hLr.trans_isBigO hu)
  refine ⟨L.comp D, hP, ?_⟩
  exact (hA.hasFDerivAt.comp x hP).unique hD

end GlobalTheory
