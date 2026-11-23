import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSign_full_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  first | exact @GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | exact GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | (intros; apply GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one <;> assumption)
