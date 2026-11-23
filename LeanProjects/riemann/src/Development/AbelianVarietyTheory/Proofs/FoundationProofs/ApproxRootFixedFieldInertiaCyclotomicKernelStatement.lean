import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxRootFixedFieldInertiaCyclotomicKernel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxRoot_fixedField_inertiaCyclotomicKernel : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) → 0 < v (l : Ω) → v (l : Ω) < 1 → ApproxRoot l v (Fix Ω (ineCyc l A)) := by
  first | (exact @GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc) | (exact GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc) | (intros; apply GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc  <;> assumption)
