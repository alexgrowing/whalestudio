import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVectorGivesLocalComponentSphericalVect
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (w : Pl E) (σ : SmIrr (UL n w)), IsCompU π w σ → IsUnramU π w → fixed σ.ρ (KL n w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | exact GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | (intros; apply GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot <;> assumption)
