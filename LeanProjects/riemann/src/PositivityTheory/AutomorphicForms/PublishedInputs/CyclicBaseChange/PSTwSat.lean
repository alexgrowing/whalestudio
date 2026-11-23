import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.STwSat_holds : UpperTheory.CBC.STwSat := by
  intro F _ _ n π η
  filter_upwards [(GlobalTheory.Mem.UnrAe.finite_ramified η).compl_mem_cofinite] with v hv
  have hu : η.UnrAt v := not_not.mp hv
  refine ⟨hu, fun B hB => ?_⟩
  cases π with
  | cx π => exact GlobalTheory.SphGal.hasSatGL_twist F n π η v B hu hB
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.twist hB hu
