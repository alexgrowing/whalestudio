import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.RenamePullLCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CardLinkIdxMulLe
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ExistsOfMemSupportLin
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PrimedEmbeddingInjective
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.OmegaValue

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem plane_gram_theorem_of_five_lemmas (h1 : 1 ≤ C0) (hV2 : V2 K) (hSPAN : SPAN K v p) (hPROJ : PROJ K v p C0)
    (hDIG : DIG K v p) (hDER : DER K v p) : LiftBoundUniform K v p C0 :=
  plane_gram_theorem_of_combined_lemmas h1 (stepBC_of (stepB_of h1 hV2 hPROJ) (stepC_of hV2 (segStep_of hSPAN)))
    (stepDEF_of h1 hDIG (stepG_of hV2) (stepP_of v p C0 h1 hPROJ) (stepE_of v p hV2 hDER))

theorem plane_gram_theorem_of_lemmas : ∀ (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
    (C0 : ℝ), LiftBoundOfHypotheses K v p C0 :=
  fun _ _ _ _ _ _ h1 hV2 hS hP hDIG hDER => plane_gram_theorem_of_five_lemmas h1 hV2 hS hP hDIG hDER

end Formalism.MainNotions.PlaneGram
