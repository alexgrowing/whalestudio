import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Wt

variable {F : Type} [Field F] [NumberField F]

def IsCuspL (n : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (inf : (F →+* ℂ) → Multiset ℂ → Prop)
    (loc : ∀ w : HeightOneSpectrum (𝓞 F), SmIrr (GL (Fin n) (w.adicCompletion F)) → Prop) : Prop :=
  (∃ (_ : IsTotallyComplex F) (π : CuspSub F n), sat = (CG.mk π).HasSat ∧ inf = π.HasInfChar ∧ loc = π.IsLocComp) ∨
    ∃ (_ : IsTotallyReal F) (π : TR.CuspSub F n), sat = π.HasSat ∧ inf = (fun τ => π.HasInfChar (InfinitePlace.mk τ)) ∧
      loc = π.IsLocComp

end UpperTheory.V.Wt
