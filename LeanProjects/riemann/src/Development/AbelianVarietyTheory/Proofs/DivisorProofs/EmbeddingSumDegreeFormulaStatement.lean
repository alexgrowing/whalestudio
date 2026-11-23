import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_sum_degree_formula : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (f : (k →+* ℂ) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  first | exact @GlobalTheory.finrank_mul_sum_embeddings_comp | exact GlobalTheory.finrank_mul_sum_embeddings_comp | (intros; apply GlobalTheory.finrank_mul_sum_embeddings_comp <;> assumption)
