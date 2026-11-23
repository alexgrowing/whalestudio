import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧ D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  first | (exact @GlobalTheory.RecOne.zeta_derivation_cyc) | (exact GlobalTheory.RecOne.zeta_derivation_cyc) | (intros; apply GlobalTheory.RecOne.zeta_derivation_cyc  <;> assumption)
