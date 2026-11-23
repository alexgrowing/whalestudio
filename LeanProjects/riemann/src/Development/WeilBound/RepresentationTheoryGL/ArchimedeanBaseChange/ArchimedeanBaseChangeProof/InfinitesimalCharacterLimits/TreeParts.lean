import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Tr.leafList : {N : ℕ} → Tr E N → List (Σ M : ℕ, Submodule ℂ (Sm E M))
  | M, .leaf V _ => [⟨M, V⟩]
  | _, .node t₁ t₂ => t₁.leafList ++ t₂.leafList

def TreeParts {N : ℕ} (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N) : Prop :=
  (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) = t.leafList.filter fun x => 0 < x.1

abbrev Carrier {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (_ : Representation ℂ G V) : Type := V

def rt {a b : ℕ} (g : Hf E a b) (F : H E a b → ℂ) : H E a b → ℂ := fun x => F (x * finH g)

def atW {a b : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    Hf E a b :=
  (locGL E a w g.1, locGL E b w g.2)

def PreOfTree : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N), t.Good → t.Untw →
  (∀ τ, ∃ m, HasInfCharGL t.space τ m) → ∃ P : PositivityTheory.Rg.BcB.F.Pre E N, TreeParts t P

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
