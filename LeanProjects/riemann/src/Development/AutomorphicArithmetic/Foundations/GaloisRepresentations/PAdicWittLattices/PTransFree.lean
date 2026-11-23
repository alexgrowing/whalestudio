import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
