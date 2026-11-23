import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryKottwitzEquivalence
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
open NumberField
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_kottwitz_equivalence : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin r) (Fin r) E), GlobalTheory.SUVol.IsSA G s → GlobalTheory.SUVol.IsSA G s' → GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M → s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s → γ.det = 1 → GlobalTheory.SUVol.SEquiv G L 1 s' s := by
  first | exact @GlobalTheory.SEquivOfRat.sequiv_of_rat | exact GlobalTheory.SEquivOfRat.sequiv_of_rat | (intros; apply GlobalTheory.SEquivOfRat.sequiv_of_rat <;> assumption)
