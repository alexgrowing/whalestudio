import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_boxes_compact_exhaust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r) ∧ ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (N : ℕ) (r x : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E), ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X ∈ box b N (Real.exp x * r) ↔ X ∈ box b N r := by
  first | exact @GlobalTheory.CompanionTheory.SW.BoxF.box_facts | exact GlobalTheory.CompanionTheory.SW.BoxF.box_facts | (intros; apply GlobalTheory.CompanionTheory.SW.BoxF.box_facts <;> assumption)
