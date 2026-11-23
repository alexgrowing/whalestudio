import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGramDeterminantBounds
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_sum_log_rootNorm_eq_neg_log_pairWeightNormSq : ∀ {T : Type} [Fintype T] {ι : Type} [Fintype ι] {N j : ℕ} (hpq : j + (N - j) = N)
    (Zm : T → (ι → ℂ) → Matrix (Fin j) (Fin (N - j)) ℂ) (GW : T → (ι → ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (GΩ : T → (ι → ℂ) → Matrix (Fin (N - j)) (Fin (N - j)) ℂ) (cW cΩ : T → ℝ) (v : ι → ℂ),
    (∀ τ, 0 < cW τ) → (∀ τ, 0 < cΩ τ) → (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) → (∀ τ, IsUnit (GW τ v).det) →
    (∀ τ, IsUnit (GΩ τ v).det) → ∀ u : T → Fin N → ℝ,
    ∑ x : T × Fin N, u x.1 x.2 * (Real.log (rootNorm N j (cW x.1) (cΩ x.1) (GW x.1 v) (GΩ x.1 v) (Zm x.1 v) x.2) / 2) =
      -Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (p := fun _ => j) (q := fun _ => N - j)
          (fun τ x => (cW τ : ℂ) • GlobalTheory.HermFrame.quotGram (modelHodgeGram (Zm τ x)))
          (fun τ x => (((cΩ τ)⁻¹ : ℝ) : ℂ) • -GlobalTheory.HermFrame.subGram (modelHodgeGram (Zm τ x))) id
          (fun τ x => (GW τ x)ᵀ) (fun τ x => ((GΩ τ x).submatrix Fin.rev id)⁻¹)
          (fun τ k => u τ (Fin.cast hpq k)) v) / 2 := by
  first | exact @GlobalTheory.HodgeLocGeo.Pointwise.pointwise | exact GlobalTheory.HodgeLocGeo.Pointwise.pointwise | (intros; apply GlobalTheory.HodgeLocGeo.Pointwise.pointwise <;> assumption)
