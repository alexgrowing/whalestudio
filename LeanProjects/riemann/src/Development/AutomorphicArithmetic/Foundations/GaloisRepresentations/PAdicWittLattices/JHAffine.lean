import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

theorem UpperTheory.Gal.G3.jHAffine :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine := by
  intro k k' _ _ φ X X' s s' g h
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
