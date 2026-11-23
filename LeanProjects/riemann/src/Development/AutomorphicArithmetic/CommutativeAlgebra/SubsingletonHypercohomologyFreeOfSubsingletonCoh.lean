import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology :
    ∀ (F : Shv ℤ) (P : PSh) (n : ℤ), Subsingleton (H ℤ (disc.obj P) F n) → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n) := by
  intro F P n hs
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf ℤ
  haveI : (res ℤ F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).1
  haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
  have hb := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso ℤ (e P).hom (res ℤ F) n
  exact hb.2.subsingleton
