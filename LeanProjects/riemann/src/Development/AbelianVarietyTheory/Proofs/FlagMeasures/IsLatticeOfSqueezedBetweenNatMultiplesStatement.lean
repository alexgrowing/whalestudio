import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiples
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples : ∀ {E : Type} [Field E] [NumberField E], ∀ (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → (∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ) → (∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) → Submodule.IsLattice E Γ := by
  first | exact @GlobalTheory.glue_latt_isLattice | exact GlobalTheory.glue_latt_isLattice | (intros; apply GlobalTheory.glue_latt_isLattice <;> assumption)
