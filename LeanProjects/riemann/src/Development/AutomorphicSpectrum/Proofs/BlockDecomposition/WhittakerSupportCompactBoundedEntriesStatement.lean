import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSupportCompactBoundedEntries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_support_compact_bounded_entries : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W₀ ∈ V', ∀ R : ℝ, ∃ C : Set (GL (Fin 2) F), IsCompact C ∧ ∀ z : GL (Fin 2) F, W₀ z ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) → (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) → z ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt.support_compact | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt.support_compact | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt.support_compact <;> assumption)
