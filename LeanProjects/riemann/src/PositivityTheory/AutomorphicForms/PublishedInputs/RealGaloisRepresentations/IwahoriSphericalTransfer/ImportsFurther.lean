import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeMultOne

theorem main : ∀ (F : Type) [Field F] [NumberField F] (η η' : HChar F), (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v) → η = η' := by
  intro F _ _ η η' h
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp h).toFinset with hS
  have key : η * η'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (η * η'⁻¹).1 (η * η'⁻¹).2.1 (η * η'⁻¹).2.2 S fun v hv => ?_)
    have hv' : η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v := by
      by_contra hc
      exact hv (by rw [hS, Set.Finite.mem_toFinset]; exact hc)
    obtain ⟨h1, h2, h3⟩ := hv'
    intro x
    refine GlobalTheory.FrobDense.eq_one_of_unif ((η * η'⁻¹).loc v) (fun y hy => ?_) x
    rw [HChar.loc_mul, HChar.loc_inv, η.val_eq h1 y hy, η'.val_eq h2 y hy, h3, mul_inv_cancel]
  exact mul_inv_eq_one.mp key

end GlobalTheory.HeckeMultOne
