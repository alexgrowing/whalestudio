import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ := by
  first | exact @GlobalTheory.LabelNorm.main | exact GlobalTheory.LabelNorm.main | (intros; apply GlobalTheory.LabelNorm.main <;> assumption)
