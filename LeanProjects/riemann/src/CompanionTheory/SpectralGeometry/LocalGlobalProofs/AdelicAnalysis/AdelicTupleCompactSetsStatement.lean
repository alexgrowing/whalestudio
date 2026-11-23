import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tuple_compact_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact {X : (Fin n → Fin M → AF F ⊗[F] E) | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r}) ∧ ∀ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ ∀ X ∈ K, (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples | exact GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples | (intros; apply GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples <;> assumption)
