import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClQuot
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.PsBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DvrBase

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cohen :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R], UpperTheory.V.CA.IsCL O R → CohenType R := by
  intro O R _ _ _ _ _ _ _ h p hp
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hS : UpperTheory.V.CA.IsCL O (R ⧸ p) :=
    UpperTheory.V.CA.cl_quot O R (R ⧸ p) (Ideal.Quotient.mkₐ O p) (Ideal.Quotient.mkₐ_surjective O p) h
  obtain ⟨h1, h2⟩ := UpperTheory.V.CA.cl_nn O (R ⧸ p) hS
  by_cases hi : Function.Injective (algebraMap O (R ⧸ p))
  · obtain ⟨d, φ, hφ, hf, -, -⟩ := h1 hi
    exact ⟨MvPowerSeries (Fin d) O, inferInstance, inferInstance, φ.toRingHom,
      psBase O (dvrBase O) d, hφ, hf⟩
  · obtain ⟨d, φ, hφ, hf, -, -⟩ := h2 hi
    exact ⟨MvPowerSeries (Fin d) (ResidueField O), inferInstance, inferInstance, φ.toRingHom,
      psBase (ResidueField O) (isBase_field _) d, hφ, hf⟩
