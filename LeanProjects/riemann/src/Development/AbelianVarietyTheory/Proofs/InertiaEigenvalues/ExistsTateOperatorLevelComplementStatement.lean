import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_operator_levelComplement : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∃ S : PadicComplex l → PadicComplex l, (∀ x ∈ Xj K j, S x ∈ Xj K j ∧ act g (S x) - S x = (ζ - 1) * x ∧ S (act g x - x) = (ζ - 1) * x) ∧ (∀ x ∈ Xj K j, ∀ x' ∈ Xj K j, S (x + x') = S x + S x') ∧ ∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, S (y * x) = y * S x := by
  first | exact @GlobalTheory.Cyc.exists_tate_operator | exact GlobalTheory.Cyc.exists_tate_operator | (intros; apply GlobalTheory.Cyc.exists_tate_operator <;> assumption)
