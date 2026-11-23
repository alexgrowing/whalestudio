import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

theorem LinesGramFischerBound.proof (h1 : LinesGramPosDef.Statement)
    (h2 : LinesFischer.Statement) (h3 : LinesDiagGram.Statement) :
    LinesGramFischerBound.Statement := by
  intro K _ n m k d σ b τ hd hτ hli
  set t : Fin k → Fin n → K := fun j => Pi.single (τ j) 1 with ht
  set h : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hh
  have hpos : h.PosDef := Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)
  have hG := h1 K n h σ (Fin m ⊕ Fin k) (Sum.elim b t) hpos hli
  have hF := h2 (Fin m) (Fin k) _ hG
  have hB1 : (gramAt h σ (Sum.elim b t)).toBlocks₁₁ = gramAt h σ b := by
    ext i j; rfl
  have hB2 : (gramAt h σ (Sum.elim b t)).toBlocks₂₂ = gramAt h σ t := by
    ext i j; rfl
  have hD : gramAt h σ t = Matrix.diagonal fun j => (d (τ j) : ℂ) := h3 K n d σ k τ hτ
  rw [hB1, hB2, hD, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re] at hF
  exact hF

end GroundTheory.Heights₂.Heights
