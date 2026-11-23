import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem mixedForms_all {W : Type} [TopologicalSpace W] {D : ℕ} (Om : ReciprocityTheory.AnForm.M.LocPot W)
    (T : Fin (D + 1) → ReciprocityTheory.AnForm.M.LocPot W) : mixedForms Om T (D + 1) = T :=
  funext fun i => if_pos i.isLt

theorem UniformIntegrability.proof (h₀ : GreenMassZero.Statement) (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement := by
  intro D W _ _ _ S
  have key : ∀ a, a ≤ D + 1 → ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε →
      ε ≤ ε₀ → 0 < t → t ≤ t₁ → S.ell₀ ≤ ell t → S.J a ε t ≤ η := by
    intro a
    induction a with
    | zero =>
      intro _ η hη
      obtain ⟨ε₀, hε₀, h⟩ := h₀ S η hη
      exact ⟨ε₀, hε₀, 1, one_pos, fun ε t hε hεle _ _ _ => h ε hε hεle t⟩
    | succ a ih =>
      intro haD η hη
      have ha : a < D + 1 := haD
      obtain ⟨Cκ, hCκ, hR⟩ := h₂ S
      have hδ : 0 < η / (2 * (Cκ + 2)) := by positivity
      obtain ⟨τ, hτ, hE⟩ := h₃ S a ha _ hδ

      have ht₀ : 0 < min τ (Real.exp (-S.ell₀)) := lt_min hτ (Real.exp_pos _)
      have hell : S.ell₀ ≤ ell (min τ (Real.exp (-S.ell₀))) := by
        have h : Real.log (min τ (Real.exp (-S.ell₀))) ≤ -S.ell₀ :=
          (Real.log_le_iff_le_exp ht₀).2 (min_le_right _ _)
        show S.ell₀ ≤ Real.log (min τ (Real.exp (-S.ell₀)))⁻¹
        rw [Real.log_inv]
        linarith
      obtain ⟨K, hK, hRK⟩ := hR a ha _ ht₀ hell
      obtain ⟨ε₁, hε₁, t₂, ht₂, hih⟩ := ih (Nat.le_of_succ_le haD) (η / (2 * (K + 1)))
        (by positivity)
      refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min t₂ (min τ (Real.exp (-S.ell₀))),
        lt_min ht₂ ht₀, ?_⟩
      intro ε t hε hεle ht htle htell
      have hJ := hih ε t hε (hεle.trans (min_le_left _ _)) ht (htle.trans (min_le_left _ _)) htell
      have hPL := h₁ S a ha ε t hε ht htell
      have hRep := hRK ε t hε (hεle.trans (min_le_right _ _)) ht (htle.trans (min_le_right _ _))
      obtain ⟨hW, hD⟩ := hE _ t ht (htle.trans (min_le_right _ _)) (min_le_left _ _) hell
      have e1 : (1 + K) * S.J a ε t ≤ η / 2 := by
        calc (1 + K) * S.J a ε t ≤ (1 + K) * (η / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left hJ (by linarith)
          _ = η / 2 := by field_simp; ring
      have e2 : Cκ * S.errW a ha (min τ (Real.exp (-S.ell₀))) t +
          2 * S.errDiv a ha (min τ (Real.exp (-S.ell₀))) t ≤ η / 2 := by
        have := mul_le_mul_of_nonneg_left hW hCκ
        calc _ ≤ Cκ * (η / (2 * (Cκ + 2))) + 2 * (η / (2 * (Cκ + 2))) := by linarith
          _ = η / 2 := by field_simp
      linarith
  intro η hη
  obtain ⟨ε₀, hε₀, t₁, ht₁, h⟩ := key (D + 1) le_rfl η hη
  refine ⟨ε₀, hε₀, t₁, ht₁, fun ε t hε hεle ht htle htell => ?_⟩
  have := h ε t hε hεle ht htle htell
  rwa [UIData.J, UIData.T, mixedForms_all] at this

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
