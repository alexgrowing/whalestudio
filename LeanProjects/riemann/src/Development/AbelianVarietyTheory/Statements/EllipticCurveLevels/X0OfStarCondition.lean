import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

def RowStarCore : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .unr π ι r w B ∧ GlobalTheory.RoadU.SphAt .dR π ι r w B ∧ GlobalTheory.RoadU.SphAt .crys π ι r w B ∧
          GlobalTheory.RoadU.SphAt .phi π ι r w B

def X0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), (CG.mk π).HasSat w B → GlobalTheory.RoadU.SphAt .unr π ι r w B

end GlobalTheory.RoadW

end
