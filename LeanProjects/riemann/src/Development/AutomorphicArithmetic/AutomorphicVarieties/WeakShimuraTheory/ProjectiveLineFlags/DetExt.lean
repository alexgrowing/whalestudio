import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.detExt :
    ∀ {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : W.GDet n A G) (f : A →+* A') (D' : W.GDet n A' G),
          (∀ g : G, (D.chi (MonoidAlgebra.single g 1)).map f = D'.chi (MonoidAlgebra.single g 1)) → D.map f = D' := by
  intro n A A' G _ _ _ D f D' h
  apply CA.d_gext
  intro g i _ _
  rw [(AlgebraTools.Det.mapApi D f).2.2.1 i g]
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one]
  rw [← Polynomial.coeff_map, h g]
