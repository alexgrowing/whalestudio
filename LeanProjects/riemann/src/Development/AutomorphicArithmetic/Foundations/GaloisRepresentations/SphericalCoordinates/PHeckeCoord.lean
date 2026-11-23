import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.heckeCoord_of :
    UpperTheory.Gal.W2.IsogAt → UpperTheory.Gal.W2.IsogCoord → UpperTheory.Gal.W2.HeckeCoord := by
  intro hA hC p _ D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU B j h₁ M hpl hco hloc
  obtain ⟨D'', t'', P'', e'', inc, d, hcls, hU'', hP, he, hd, hinc, f, nu, f'', nu'', hw, hw'', hf, hf'', hiff⟩ :=
    hA p D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨h3, hNp, h3', hNp', -, hK⟩ := hlev
  obtain ⟨j'', hj, hpl'', hco'', hloc''⟩ :=
    hC p D G L B N N' (by omega) hNp (by omega) hNp' h hK ρ D' t D'' t'' P P'' inc d hU.2.1 hU''.2.1 hP hd hinc
      f nu f'' nu'' hw hw'' hf hf'' hiff j h₁ M hpl hco hloc
  refine ⟨D'', t'', P'', e'', inc, j'', hcls, hU'', hP, he, ?_, hj, hpl'', hco'', hloc''⟩
  intro u''
  obtain ⟨u, hu⟩ := hinc u''
  refine ⟨d, u, ?_, hu⟩
  rintro rfl
  have hp : p = 1 := by simpa using hd
  exact (Fact.out : p.Prime).one_lt.ne' hp
