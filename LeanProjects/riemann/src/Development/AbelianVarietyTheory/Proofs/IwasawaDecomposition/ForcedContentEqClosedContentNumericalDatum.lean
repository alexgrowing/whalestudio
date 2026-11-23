import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

theorem forcedContent_eq_closedContent_numericalDatum : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), DV.KapDef D →
    ∀ (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m),
      GlobalTheory.Mem.Top.Bl.F0K L.sc D y j = (ofRecord D L Del h0).Fj (j.1 + 1) y :=
  fun D L Del h0 hK y j => (ofRecord_Fj_succ D L Del h0 hK y j).symm

end GlobalTheory.Mem.Top.Bl
