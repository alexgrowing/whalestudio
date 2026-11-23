import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_parahoricBiTransforming_doubleCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ Blocks l t) k → ℂ, IsBiType ξ φ →
    (∀ x y, φ (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧ g ∈ dcell ϖ (e ∘ (blkEquiv l t).symm) := by
  first | exact @GlobalTheory.ChainStepSupp.support_dcell | exact GlobalTheory.ChainStepSupp.support_dcell | (intros; apply GlobalTheory.ChainStepSupp.support_dcell <;> assumption)
