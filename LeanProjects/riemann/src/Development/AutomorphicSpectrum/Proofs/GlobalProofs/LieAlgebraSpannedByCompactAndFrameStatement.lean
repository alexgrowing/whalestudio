import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraSpannedByCompactAndFrame
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_spanned_by_compact_and_frame : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ → ∃ (n₁ n₂ : ℕ) (X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ a, X a ∈ lieAt V τ) ∧ (∀ b, GlobalTheory.CompanionTheory.HCCusp.IsKLie e (y b)) ∧ (∀ Z ∈ lieAt V τ, Z ∈ Submodule.span ℝ (Set.range X ∪ Set.range fun b => P⁻¹ * y b * P)) ∧ ∀ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, gelf θ V τ 1 f = ∑ a, Rder θ V τ (X a) (Rder θ V τ (X a) f) - ∑ b, Rder θ V τ (P⁻¹ * y b * P) (Rder θ V τ (P⁻¹ * y b * P) f) := by
  first | exact @GlobalTheory.CompanionTheory.HCCusp.quadGelf_frame | exact GlobalTheory.CompanionTheory.HCCusp.quadGelf_frame | (intros; apply GlobalTheory.CompanionTheory.HCCusp.quadGelf_frame <;> assumption)
