import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetWordMultiplicity_additive_jordanHolder : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  first | exact @GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | exact GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | (intros; apply GlobalTheory.SmGL.Exponents.Additive.wordMult_additive <;> assumption)
