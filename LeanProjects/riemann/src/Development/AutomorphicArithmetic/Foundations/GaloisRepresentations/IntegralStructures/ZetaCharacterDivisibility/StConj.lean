import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cpl (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) := conjSrc (GlobalTheory.SplitPts.conjE E) w

omit [NumberField E] [IsCMField E] in

def SameK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def CplMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (y y' : 𝓞 E),
    (y' : E) = IsCMField.complexConj E (y : E) → (y ∈ (cpl w).asIdeal ↔ y' ∈ w.asIdeal)

def SameOr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l d : ℕ), l.Prime → 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ w w' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ((l : ℕ) : 𝓞 E) ∈ w'.asIdeal → SameK x w w' ∨ SameK x (cpl w) w'

def LocIso : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
    locU (E := E) a (cpl w) = locU a w ∧
    ∃ β : GL (Fin a) ((cpl w).adicCompletion E) ≃ₜ* GL (Fin a) (w.adicCompletion E),
      (∀ x : UA E a, β (cLoc (cpl w) x) = cLoc w x) ∧ (∀ g, g ∈ GlobalTheory.LFun.KGL (cpl w) a → β g ∈ GlobalTheory.LFun.KGL w a) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V),
        GlobalTheory.SmGL.IsCuspidal σ → GlobalTheory.SmGL.IsCuspidal (σ.comp β.toMulEquiv.toMonoidHom)

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ B, SatU U w B) → ∃ B, SatU U (cpl w) B

def TyConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ) (U : Submodule ℂ (UA E a → ℂ))
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → GlobalTheory.CongW.TyEll E l a w U → GlobalTheory.CongW.TyEll E l a (cpl w) U

def LacConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (U : Submodule ℂ (UA E a → ℂ)) (v : HeightOneSpectrum (𝓞 E)), LacWtAt ι v U → LacWtAt ι (cpl v) U

def GapLac : Prop := ∀ (a : ℕ) (J : Finset ℤ), J.card = a → GapJ a J.val → Lacunary J

end UpperTheory.Gal.Int.Div

end
