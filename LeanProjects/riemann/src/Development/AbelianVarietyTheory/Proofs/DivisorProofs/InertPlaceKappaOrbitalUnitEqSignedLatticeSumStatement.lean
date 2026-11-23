import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_kappaOrbital_unit_eq_signedLatticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Monic → Q₂.Monic → Q₁.natDegree + Q₂.natDegree = n → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → ∀ B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → B₁.P = Q₁.map e.symm.toRingHom → B₂.P = Q₂.map e.symm.toRingHom → kapOrb n w Q₁ Q₂ ((KL n w : Set (UL n w)).indicator 1) = (B₁.kapSum B₂ : ℂ) := by
  first | exact @GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum | exact GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum | (intros; apply GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum <;> assumption)
