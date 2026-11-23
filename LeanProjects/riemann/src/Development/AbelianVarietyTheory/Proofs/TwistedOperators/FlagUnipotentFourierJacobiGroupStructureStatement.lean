import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_unipotent_fourier_jacobi_group_structure : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ n, n ∈ flagN d ↔ ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c)) ∧ (∀ n, n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c) ∧ (∀ g, g ∈ stabX d ↔ ∃ n ∈ radX d, ∃ h, g = n * d.emb0 h) ∧ (∀ g, g ∈ jacGrp d ↔ ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h) ∧ (∀ n ∈ flagN d, ∀ h, d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ∀ h h', n * d.emb0 h = n' * d.emb0 h' → n = n' ∧ h = h') ∧ ∀ u b c u' b' c', d.levi u * (d.nB b * d.nC c) = d.levi u' * (d.nB b' * d.nC c') → u = u' ∧ b = b' ∧ c = c' := by
  first | exact @GlobalTheory.MixPer.flag_jacobi_structure | exact GlobalTheory.MixPer.flag_jacobi_structure | (intros; apply GlobalTheory.MixPer.flag_jacobi_structure <;> assumption)
