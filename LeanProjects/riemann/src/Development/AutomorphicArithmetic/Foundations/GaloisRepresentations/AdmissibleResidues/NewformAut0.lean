import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
open UpperTheory.GalN.V

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Af.NewformAutomorphy

end UpperTheory.V.Af.NewformAutomorphy

theorem UpperTheory.GalN.V.newformAut0 :
    UpperTheory.V.Af.Hypotheses₂ → NewformAut0 := by
  intro P k hk f l hl Ω _ _ _ ι W j hf hW K _ _ _ _ _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact UpperTheory.V.Sd.upQuad P ℚ K Ω l ι hK 2 one_le_two W hW (UpperTheory.V.Af.newformAutR P k hk f l Ω ι W j hf) hirr
