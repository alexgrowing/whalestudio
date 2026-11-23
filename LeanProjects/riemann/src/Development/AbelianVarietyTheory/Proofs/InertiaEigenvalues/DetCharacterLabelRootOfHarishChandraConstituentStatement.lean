import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]), IsIrr ψ →
    HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g), GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  first | exact @GlobalTheory.GLq.DetRoot.root_of_hc_det | exact GlobalTheory.GLq.DetRoot.root_of_hc_det | (intros; apply GlobalTheory.GLq.DetRoot.root_of_hc_det <;> assumption)
