import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFormulaSqrtNormalizedAbsValuesCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolysStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodEqFinprodMemFibresOfSectionStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm
theorem resNe : ∀ (K : Type) [Field K] (P Q : K[X]), P.Monic → Q.Monic → IsCoprime P Q → resultant P Q ≠ 0 := by
  intro K _ P Q _ _ hc
  exact Polynomial.resultant_ne_zero P Q hc

theorem resMap : ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (P Q : K[X]),
    resultant (P.map f) (Q.map f) = f (resultant P Q) := by
  intro K L _ _ f P Q
  rw [Polynomial.natDegree_map, Polynomial.natDegree_map]
  exact Polynomial.resultant_map_map P Q _ _ f
end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

end GlobalTheory.ProdForm
