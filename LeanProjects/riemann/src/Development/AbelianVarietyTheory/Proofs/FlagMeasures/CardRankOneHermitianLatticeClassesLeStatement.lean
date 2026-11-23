import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  first | exact @GlobalTheory.RankOneClasses.card_classes_le | exact GlobalTheory.RankOneClasses.card_classes_le | (intros; apply GlobalTheory.RankOneClasses.card_classes_le <;> assumption)
