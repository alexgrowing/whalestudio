import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt

noncomputable section

namespace Formalism.L2.Pj

open NumberField

section

variable {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)

instance (priority := high) rulesCommRing : CommRing (Rules pts) := inferInstance
instance (priority := high) rulesAlgebra : Algebra K (Rules pts) := inferInstance
instance (priority := high) rulesModule : Module K (Rules pts) := inferInstance
instance (priority := high) rulesSMul : SMul K (Rules pts) := inferInstance
instance (priority := high) rulesAlgebraInt : Algebra (𝓞 K) (Rules pts) := inferInstance
instance (priority := high) rulesModuleInt : Module (𝓞 K) (Rules pts) := inferInstance
instance (priority := high) rulesTower : IsScalarTower (𝓞 K) K (Rules pts) := inferInstance

end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

example : Algebra c.F (Rul Xo c) := inferInstance
example : Algebra (𝓞 c.F) (Rul Xo c) := inferInstance
example : IsScalarTower (𝓞 c.F) c.F (Rul Xo c) := inferInstance
example (a : c.F) (f : Rul Xo c) : Rul Xo c := a • f
example (a : 𝓞 c.F) (f : Rul Xo c) : Rul Xo c := a • f

end Formalism.L2.Pj
