import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapOfSymmetricComparisonLowerMapFiniteChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem formsMap_at_every_trueColumnMember : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  intro B X I hOk hP l Z u
  obtain ⟨C, hC, -⟩ := GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hOk hP l Z
  have hF := hC u
  have hL := GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie I hOk hP l Z u _ _ (C.forms u) hF
  have hB := GlobalTheory.Mem.Col2.TC.beOnTie_true I hOk hP l Z u
  have hR : ∀ i, (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧
      ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) :=
    fun i => GlobalTheory.trueCols_exists_primitiveRoots I hOk l Z i
  exact GlobalTheory.RedPt0.formsMap_of_symmetricComparison_lowerMap_finiteChar (I.rec7 l Z) u _ _ (C.forms u) hL hB
    (GlobalTheory.chi_last_step_finite_order_symTie (I.rec7 l Z) u _ _ (C.forms u) hR)

end GlobalTheory.Mem.Col2.TC
