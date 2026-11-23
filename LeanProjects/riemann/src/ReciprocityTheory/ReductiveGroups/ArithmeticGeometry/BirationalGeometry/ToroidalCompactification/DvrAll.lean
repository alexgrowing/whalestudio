import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem dvrDataAt_all (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (h3 : Y.N3) (P : ValPt Y) : DvrDataAt P :=
  dvrData_of_splitting h3 P (splitsAt hC hU hB hS P)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
