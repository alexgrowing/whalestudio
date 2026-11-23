import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.cupEx_holds :
    UpperTheory.Gal.KunnethLefschetz.CupEx := by
  intro hB l _ K M i j x y
  exact ⟨LateralTheory.EtaleTrace.LRingPf.cupL l M.spc (Nat.cast_add i j).symm hB x y,
    fun k => LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc (Nat.cast_add i j).symm hB x y k⟩
