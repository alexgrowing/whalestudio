import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_element_basis_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  first | exact @GlobalTheory.TwLat.isUnit_gram_of_separable | exact GlobalTheory.TwLat.isUnit_gram_of_separable | (intros; apply GlobalTheory.TwLat.isUnit_gram_of_separable <;> assumption)
