import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSection
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germSections_halfPlane_global_section : ∀ (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ), (∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') → (∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) → ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  first | exact @GlobalTheory.germSections_halfPlane_global | exact GlobalTheory.germSections_halfPlane_global | (intros; apply GlobalTheory.germSections_halfPlane_global <;> assumption)
