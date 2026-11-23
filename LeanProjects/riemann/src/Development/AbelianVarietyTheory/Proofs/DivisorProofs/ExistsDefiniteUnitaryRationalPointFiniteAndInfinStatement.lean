import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  first | exact @GlobalTheory.BCT.RatPt.ratPt | exact GlobalTheory.BCT.RatPt.ratPt | (intros; apply GlobalTheory.BCT.RatPt.ratPt <;> assumption)
