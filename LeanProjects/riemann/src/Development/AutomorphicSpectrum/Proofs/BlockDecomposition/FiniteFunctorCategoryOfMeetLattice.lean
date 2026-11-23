import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem finite_chains_semilattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ),
    Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  intro P _ _ p
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun F : Fin (p + 1) ⥤ Pᵒᵖ => F.obj) ?_
  intro F G h
  exact CategoryTheory.Functor.ext (fun i => congrFun h i)
    (fun i j f => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end GlobalTheory.CompanionTheory.HopfC
