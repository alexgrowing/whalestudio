import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_ordL_conjGramDet_of_unit_gram_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι (w.adicCompletion E) V)
    (c : Module.Basis κ (w.adicCompletion E) V),
    Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → w.adicCompletion E) k) * (c j : Fin n → w.adicCompletion E) k).det = 1 →
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k).det = 1 := by
  first | exact @GlobalTheory.GramParity.gram_det_parity | exact GlobalTheory.GramParity.gram_det_parity | (intros; apply GlobalTheory.GramParity.gram_det_parity <;> assumption)
