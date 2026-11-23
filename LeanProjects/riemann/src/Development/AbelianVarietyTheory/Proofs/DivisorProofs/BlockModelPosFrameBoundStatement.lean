import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_model_pos_frame_bound : ∀ (e m : ℕ) (σ : Fin m → Option (Fin e)) (ι : Type) [Fintype ι] (μ : ι → ℕ) (ρ : ℝ) (U : Set (Fin e → ℂ)) (H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), 0 < ρ → punct σ ρ ⊆ U → IsBlockModel ρ U H → ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ τ, GlobalTheory.HermFrame.IsPosFrame (punct σ ρ') (H τ) ∧ GlobalTheory.HermFrame.OneFormBound (punct σ ρ') (fun _ => (1 : Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ)) (modelGram σ) (GlobalTheory.HermFrame.conn (H τ)) C ∧ GlobalTheory.HermFrame.TwoFormBound (punct σ ρ') (H τ) (modelGram σ) (GlobalTheory.HermFrame.curv (H τ)) C := by
  first | exact @GlobalTheory.CurvInterp.Block.blockModel_bounds | exact GlobalTheory.CurvInterp.Block.blockModel_bounds | (intros; apply GlobalTheory.CurvInterp.Block.blockModel_bounds <;> assumption)
