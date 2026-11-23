import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ) (ξ μ₀' : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → IsUnram μ₀' → IsUnitaryChar μ₀' →
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let c : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => ip ν (om μ' g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) Φ) Φ
  IsBiType ξ c ∧
  (∀ x y, c (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) ∧
  ∀ e : Blocks l t → ℤ, c (mtor ϖ e) = (μ' ϖ : ℂ) ^ (∑ i, e i) *
    ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) *
    (resCard k : ℂ) ^ (-((r + (l + 1) * t : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  first | exact @GlobalTheory.ChainStepCoef.coef | exact GlobalTheory.ChainStepCoef.coef | (intros; apply GlobalTheory.ChainStepCoef.coef <;> assumption)
