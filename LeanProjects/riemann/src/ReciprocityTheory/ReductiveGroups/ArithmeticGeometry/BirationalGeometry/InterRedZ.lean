import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem poincareLelong_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hPL : ReciprocityTheory.AnForm.M.PoincareLelongStatement) (hPush : ResDivPushStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution_atlas hE hB hPL ReciprocityTheory.AnForm.M.sncInducedAtlas hPush

theorem stokes_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement) : StokesStatement :=
  stokes_of'' hE hB ReciprocityTheory.AnForm.M.byPartsSymm

theorem poincareLelong_of_resolution_pushforward (hE : ResExistsStatement) (hB : ResBridgeStatement) (hPush : ResDivPushStatement) :
    ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution hE hB ReciprocityTheory.AnForm.M.poincareLelong hPush

end ReciprocityTheory.ChartRestriction.G.Geo
