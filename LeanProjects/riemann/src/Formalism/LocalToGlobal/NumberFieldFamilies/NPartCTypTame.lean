import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace Formalism.L2.Fam.NPCTyp

open Formalism.BasicNotions Formalism.L2.NT

def zetaC (g : ℕ) [Fact g.Prime] : ℕ → Formalism.CyclotomicNorms.Fbar g :=
  Classical.epsilon fun ζ : ℕ → Formalism.CyclotomicNorms.Fbar g => IsGenSys ζ

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def TgSpec (A : ValuationSubring Ω) (g : ℕ) [Fact g.Prime] (σ : G E Ω) : Prop :=
  TameGenAt A σ ∧ ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, TameCoupled A κ σ (zetaC g)

def tgC (A : ValuationSubring Ω) (g : ℕ) [Fact g.Prime] : G E Ω :=
  @Classical.epsilon _ ⟨1⟩ (TgSpec A g)

def gamG {R : Ranks} (H : Host R) {Om : Type} [Field Om] [Algebra H.E Om] (plOm : Formalism.GaloisCohomology.Places H.E Om)
    (dflt : HeightOneSpectrum (𝓞 H.E) → G H.E Om) (v : HeightOneSpectrum (𝓞 H.E)) : G H.E Om :=
  open Classical in
  if v ∈ placesOver H.E (H.g 0) then (haveI : Fact (H.g 0).Prime := ⟨H.g_prime 0⟩; tgC (plOm.1 v) (H.g 0))
  else if v ∈ placesOver H.E (H.g 1) then (haveI : Fact (H.g 1).Prime := ⟨H.g_prime 1⟩; tgC (plOm.1 v) (H.g 1))
  else dflt v

end Formalism.L2.Fam.NPCTyp
