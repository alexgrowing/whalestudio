import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ), (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧ Submodule.span ℂ (Set.range φ) = ⊤ := by
  first | exact @GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | exact GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | (intros; apply GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix <;> assumption)
