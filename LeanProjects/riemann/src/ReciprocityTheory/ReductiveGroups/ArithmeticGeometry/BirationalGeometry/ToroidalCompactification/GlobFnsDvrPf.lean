import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open ReciprocityTheory.ChartRestriction.G.Out

theorem globalFnsDvr_of_globalFns (hGF : GlobalFnsSt) : GlobalFnsDvrSt := by
  intro E _ _ _ H V _ _ _ _hcomp t hprop n
  letI : GrpObj t.G := t.grp
  have hsemi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hsemi.smooth
  haveI : IsSeparated t.G.hom := hsemi.separated
  haveI : QuasiCompact t.G.hom := hsemi.quasiCompact
  obtain ⟨h1, h2, h3⟩ := GlobalFunctionsDvrGeneric.powObj_props t.G n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := hprop
  have hK := GlobalFunctionsDvrPowers.pull_powObj_globalFns hGF
    (spMap (algebraMap V (FractionRing V))) t.G hsemi n
  exact GlobalFunctionsDvrGeneric.bij_of_generic (powObj t.G n) hK

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
