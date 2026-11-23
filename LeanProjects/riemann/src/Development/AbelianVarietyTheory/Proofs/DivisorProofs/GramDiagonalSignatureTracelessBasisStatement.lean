import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDiagonalSignatureTracelessBasis
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
open NumberField Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_diagonal_signature_traceless_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → G.det ≠ 0 → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ i, (e i).trace = 0 ∧ ∀ u w, ReciprocityTheory.ChartRestriction.G.FD.herm G (e i *ᵥ u) w + ReciprocityTheory.ChartRestriction.G.FD.herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → GlobalTheory.SUVol.riemLie Ψ G x = ENNReal.ofReal (Real.sqrt ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • GlobalTheory.SUVol.formLie Ψ e := by
  first | exact @GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs | exact GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs | (intros; apply GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs <;> assumption)
