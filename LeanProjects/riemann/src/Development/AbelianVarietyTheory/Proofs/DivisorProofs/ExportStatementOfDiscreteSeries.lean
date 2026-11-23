import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowStatementOfLowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideOfTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistLowerBoundStatement

set_option autoImplicit false

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem exportSt_of_hypotheses (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : ExportSt :=
  have tA := GlobalTheory.T.twAdm'
  have tC := GlobalTheory.T.twist_character_of_artin hA tA
  have row := GlobalTheory.T.row_statement_of_low_weight hC hA hR hS GlobalTheory.T.low_weight_statement tA
  Steps.exportSt ⟨GlobalTheory.T.canonical_existence, GlobalTheory.T.canonical_projection, tA, row, GlobalTheory.T.rationality_of_twist_row tA row, GlobalTheory.T.reciprocity_side_of_twist tA, GlobalTheory.T.adapted_existence,
    GlobalTheory.T.conjugate_base_of_reciprocity hC hA hR hS, GlobalTheory.T.conjugate_twist_of_discrete_series hC hA hR hD hW hS tA tC, GlobalTheory.T.base_upper_bound hC hA hR, GlobalTheory.T.base_lower_bound hC hA hR hS,
    GlobalTheory.T.twist_upper_bound hC hA hR tA tC, GlobalTheory.T.twGe_of_print_twAdm_twChr hC hA hR hS tA tC⟩

end GlobalTheory.BigOn.Exp
