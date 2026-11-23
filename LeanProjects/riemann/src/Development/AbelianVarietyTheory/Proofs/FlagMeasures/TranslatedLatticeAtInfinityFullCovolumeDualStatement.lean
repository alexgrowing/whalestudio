import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ κ : ℝ, 0 < κ ∧ ∀ g : MatInf E j, 0 < detNorm E j g → (∃ _ : DiscreteTopology (latAt E j Λ g), IsZLattice ℝ (latAt E j Λ g)) ∧ covAt E j (latAt E j Λ g) = κ / detNorm E j g ∧ covAt E j (dualAt E j (latAt E j Λ g)) = (covAt E j (latAt E j Λ g))⁻¹ ∧ dualAt E j (dualAt E j (latAt E j Λ g)) = latAt E j Λ g) ∧ covAt E j (latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E))) fun _ a b => if a = b then 1 else 0) = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j) := by
  first | exact @GlobalTheory.LatFacts.lattice_facts | exact GlobalTheory.LatFacts.lattice_facts | (intros; apply GlobalTheory.LatFacts.lattice_facts <;> assumption)
