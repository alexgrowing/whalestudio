import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShearIsoActionProjection
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_iso_action_projection : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | exact GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd <;> assumption)
