import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBaseChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def QuadBC0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (a : ℕ) [Fact (a = 2)], 1 ≤ a → ∀ π : TR.CuspSub F a, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E a, IsBC0 π P

theorem quadBC0_of_quadBaseChange (h : QuadBaseChange) : QuadBC0 := fun F E _ _ _ _ _ _ _ h2 a _ ha π _ =>
  (h F E h2 a ha π).imp_right fun ⟨P, hP⟩ => ⟨P, hP.inf, hP.unr⟩

theorem quadBC0_of_two (h : Z.Bc.QuadBC2) : QuadBC0 := by
  intro F E _ _ _ _ _ _ _ h2 a ha _ π hr
  obtain rfl := ha.out
  exact (h F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, hP.inf, hP.unr⟩

end UpperTheory.V.Br
