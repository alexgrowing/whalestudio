import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af
open UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def LiftC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    [IsGalois F E], (Module.finrank F E).Prime → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub F a, (CG.mk π).IsRegAlg →
      (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨ ∃ P : CuspSub E a,
        (∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧
        WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

end UpperTheory.V.Z.Bc
