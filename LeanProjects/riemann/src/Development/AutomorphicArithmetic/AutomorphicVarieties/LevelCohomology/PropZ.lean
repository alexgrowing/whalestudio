import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.propZ :
    HV.PropZ := by
  intro Ω _ _ _ l _ c e h5 h2 hev hd
  by_cases h : l - 1 ∣ e
  · exact UpperTheory.V.X.zOne Ω l c.O (by omega) e (by omega) h
  · exact UpperTheory.V.X.zQuad Ω l c.O h5 e hev hd h
