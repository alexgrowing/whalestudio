import Formalism.LocalToGlobal.ProjectiveLattices.ModelDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace ZetaZeros.MainNotions.AbelianModels

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def AbelianLocalSystemsExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), AbelianAtQZero Dw

end ZetaZeros.MainNotions.AbelianModels
