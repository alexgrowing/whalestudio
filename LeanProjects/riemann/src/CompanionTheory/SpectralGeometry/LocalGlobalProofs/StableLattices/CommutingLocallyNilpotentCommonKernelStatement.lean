import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_locally_nilpotent_common_kernel : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ → ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) → (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) → ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) → ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | exact GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | (intros; apply GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family <;> assumption)
