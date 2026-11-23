import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FiberTwo

theorem eq_or_eq_of_under_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E) (hu : u ≠ w)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)))
    (h' : u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u' = w ∨ u' = u := by
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hc := IsCMField.complexConj_ne_one (K := E)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u).1 h with h1 | h1
  · exact absurd h1 hu
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u').1 h' with h2 | h2
  · exact Or.inl h2
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h2 h1)

end GlobalTheory.BCT.FiberTwo
