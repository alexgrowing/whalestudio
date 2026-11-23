import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclicStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.acy_mappingCone_semiMap_of_injective :
    ∀ (R : Type) [CommRing R] (L B : Cx R), (∀ s, Injective (L.X s)) → (∀ s, Injective (B.X s)) → ∀ (ρ : SemiMap L B) (Q : Scheme.{0} → Prop) (s : ℤ), Acy Q ((mappingCone ρ.toZ).X s) := by
  intro R _ L B hL hB ρ Q s
  have key : ∀ (I : Shv R), Injective I → Acy Q ((restr (Int.castRingHom R)).obj I) := by
    intro I hI P _ n hn
    exact UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology _ P n (GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R _ I P n hn)
  exact UpperTheory.acy_middle_of_shortExact Q _ (mappingCone.triangleRotateShortComplexSplitting ρ.toZ s).shortExact
    (key _ (hB s)) (key _ (hL (s + 1)))
