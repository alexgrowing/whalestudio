import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

theorem iteratedDeriv_expG_line_eq_rightDeriv_pow :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  intro 𝔸 _ _ _ _ G 𝔤 h f hf X g n
  have hd : ∀ (f : G → ℂ), h.IsSmoothFun f → ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f (g * h.expG (s • X))) s := by
    intro f hf s
    have h1 := h.hasDerivAt_rightDeriv hf X (g * h.expG (s • X))
    have h2 : HasDerivAt (fun t : ℝ => f (g * h.expG ((s + t) • X)))
        (h.rightDeriv X f (g * h.expG (s • X))) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ (n : ℕ) (f : G → ℂ), h.IsSmoothFun f →
      iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X)))
        = fun s : ℝ => (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
    intro n
    induction n with
    | zero => intro f _; simp
    | succ n ih =>
      intro f hf
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun t : ℝ => f (g * h.expG (t • X)))
          = fun t : ℝ => h.rightDeriv X f (g * h.expG (t • X)) := by
        funext s; exact (hd f hf s).deriv
      rw [hderiv, ih _ (h.isSmoothFun_rightDeriv hf X)]
      funext s
      rw [List.replicate_succ', List.foldr_append]
      rfl
  refine ⟨?_, fun s => by rw [hi n f hf]⟩
  have hc := (h.isSmoothFun_iff).1 hf g
  exact hc.comp (contDiff_id.smul contDiff_const)

end GlobalTheory
