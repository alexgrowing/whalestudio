import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_contDiff_line :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ _ S _ hS K _ Λ hΛ l i f hf
  have hd : ∀ (l : List (Fin d)) (s : ℝ), HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) s := by
    intro l s
    have h1 := hΛ.der l i _ (hS f hf (h.expG (s • b i)))
    have h2 : HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG ((s + t) • b i) * y))
        (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ p : ℕ, iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      = fun s : ℝ => Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hd _ s).deriv, List.replicate_succ, List.cons_append]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun p s => by rw [hi p]⟩
  rw [hi m]
  exact fun s => (hd _ s).differentiableAt

end GlobalTheory.HCA
