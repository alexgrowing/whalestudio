import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (H : Subgroup (G ℚ Ω)), H ≤ Dec (F := ℚ) A → ∀ (m : ℕ) (x : Ω), x ∈ A →
  (∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) → ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  first | exact @GlobalTheory.AxSen.exists_fixed_congr | exact GlobalTheory.AxSen.exists_fixed_congr | (intros; apply GlobalTheory.AxSen.exists_fixed_congr <;> assumption)
