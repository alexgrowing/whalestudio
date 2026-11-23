import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → ∀ i k : Ix Ψ j j', (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff <;> assumption)
