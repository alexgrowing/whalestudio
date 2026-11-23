import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rankAtStalk_eq_of_finrank_fibres :
    ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K]
      [Module.Projective R K] (g : ℕ),
      (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  intro R K _ _ _ _ _ g hg p
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] K) :=
    Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_tensorProduct,
    ← Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K).finrank_eq]
  exact hg _

end GlobalTheory.CompanionTheory.PerfVB
