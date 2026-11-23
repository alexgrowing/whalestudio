import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

instance factTwo : Fact ((2 : ℕ) = 2) := ⟨rfl⟩

def GaloisRepRankTwoReal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) [Fact (a = 2)], 1 ≤ a →
    ∀ (π : TR.CuspSub F a) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
      ∃ (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRepOfR π ι r wt HT

def QuadBC2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ π : TR.CuspSub F 2, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E 2, IsBC π P

theorem galoisRepRankTwoReal_of (h : GaloisRepReal) : GaloisRepRankTwoReal := fun F Ω _ _ _ _ _ _ l _ ι a _ => h F Ω l ι a

end UpperTheory.V.Z.Bc
