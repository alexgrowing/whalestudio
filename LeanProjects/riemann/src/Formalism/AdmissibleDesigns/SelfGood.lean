import Formalism.AdmissibleDesigns.NonemptyPl

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.N

def SelfGood {D : D7} (i : D.nd.Loc) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).IsGood

end Formalism.MainNotions.N.K

end
