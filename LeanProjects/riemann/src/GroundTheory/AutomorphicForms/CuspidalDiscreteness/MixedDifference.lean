import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum

namespace GroundTheory.Automorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_sub_translate_le {k : ℕ} {ρ : E → F} (hρ : ContDiff ℝ (k + 1) ρ)
    {B : ℝ} (hB : ∀ w, ‖iteratedFDeriv ℝ (k + 1) ρ w‖ ≤ B) (y w : E) :
    ‖iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w‖ ≤ B * ‖y‖ := by
  have h1 : ContDiff ℝ k ρ := hρ.of_le (by exact_mod_cast Nat.le_succ k)
  have h2 : ContDiff ℝ k (fun t => ρ (t + y)) := h1.comp (contDiff_id.add contDiff_const)
  have hsub : iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w =
      iteratedFDeriv ℝ k ρ (w + y) - iteratedFDeriv ℝ k ρ w := by
    have := iteratedFDeriv_sub_apply (x := w) (i := k) h2.contDiffAt h1.contDiffAt
    rw [show (fun t => ρ (t + y) - ρ t) = (fun t => ρ (t + y)) - ρ from rfl, this,
      iteratedFDeriv_comp_add_right]
  rw [hsub]
  have hdiff : Differentiable ℝ (fun x => iteratedFDeriv ℝ k ρ x) :=
    hρ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun x => iteratedFDeriv ℝ k ρ x) (x := w) (y := w + y) (C := B)
    (fun x _ => hdiff x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB x)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa using this

theorem norm_altSum_le : ∀ (k : ℕ) {ρ : E → F}, ContDiff ℝ k ρ → ∀ {B : ℝ},
    (∀ w, ‖iteratedFDeriv ℝ k ρ w‖ ≤ B) → ∀ (v : Fin k → E) (z : E),
      ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖
  | 0, ρ, _, B, hB, v, z => by
    simpa [norm_iteratedFDeriv_zero] using hB z
  | k + 1, ρ, hρ, B, hB, v, z => by
    rw [altSum_succ, Fin.prod_univ_succ, ← mul_assoc]
    have hg : ContDiff ℝ k (fun t => ρ (t + v 0) - ρ t) :=
      ((hρ.of_le (by exact_mod_cast Nat.le_succ k)).comp (contDiff_id.add contDiff_const)).sub
        (hρ.of_le (by exact_mod_cast Nat.le_succ k))
    exact norm_altSum_le k hg (fun w => norm_iteratedFDeriv_sub_translate_le hρ hB (v 0) w)
      (Fin.tail v) z

theorem exists_norm_altSum_le {ρ : E → F} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (k : ℕ) :
    ∃ B : ℝ, ∀ (v : Fin k → E) (z : E), ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖ := by
  have hcont : Continuous fun x => iteratedFDeriv ℝ k ρ x :=
    hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv k)
  exact ⟨B, norm_altSum_le k (hρ.of_le (by exact_mod_cast le_top)) hB⟩

end GroundTheory.Automorphic
