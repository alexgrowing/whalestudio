import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (M : Type) [AddCommGroup M] (u : G ℚ Ω → M), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → (∀ x : M, l ^ n • x = 0) → IsLocallyConstant (fun s : Ine (F := ℚ) B => u s) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, u (s * t) = u s + u t) → ∀ g ∈ Dec (F := ℚ) B, ∀ s ∈ Ine (F := ℚ) B, u (g * s * g⁻¹) = u s := by
  first | exact @GlobalTheory.TameConjInv.conj_invariant | exact GlobalTheory.TameConjInv.conj_invariant | (intros; apply GlobalTheory.TameConjInv.conj_invariant <;> assumption)
