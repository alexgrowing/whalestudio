import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.SqInt

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem memLp_two_of_cpt : LgFacts → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f → MemLp (fun y : G n => f y.val) 2 μ := by
  intro hL n _ _ μ _ V _ _ f hf hc
  obtain ⟨R, hR⟩ := hc
  have hmem : ∀ y : G n, y.val ∈ GLs n := fun y =>
    ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hcont : Continuous fun y : G n => f y.val :=
    hf.continuousOn.comp_continuous Units.continuous_val hmem
  have hsupp : HasCompactSupport fun y : G n => f y.val :=
    HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => hR _ (hmem y) (not_le.1 hy)
  have : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (G n) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact hcont.memLp_of_hasCompactSupport hsupp

end GlobalTheory.CompanionTheory.WaveCp.SqInt
