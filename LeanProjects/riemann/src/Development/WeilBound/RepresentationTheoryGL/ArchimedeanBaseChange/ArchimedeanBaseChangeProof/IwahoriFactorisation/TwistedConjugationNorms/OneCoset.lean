import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def OneCoset (θ : G →* G) (I : Subgroup G) (δ : G) (X : Set G) (p₀ : G) : Prop :=
  (∀ p : G, p⁻¹ * δ * θ p ∈ X ↔ ∃ z ∈ twCent θ δ, ∃ i ∈ I, p = z * p₀ * i) ∧
    cptPart (twCent θ δ) ≤ I.map (MulAut.conj p₀).toMonoidHom

def CentOK (θ : G →* G) (K I : Subgroup G) (δ : G) : Prop :=
  ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧
    (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def TO (n : ℕ) (w : Pl E) : Set (GLw n w) :=
  {g | (∀ i j : Fin n, i ≠ j → g.val i j = 0) ∧ ∀ i, Valued.v (g.val i i) = 1}

def nv {a : ℕ} (y : Fin a → ℤ) (i : Fin a) : ℤ := y i - y i.rev

def CaseA (w : Pl E) (n a : ℕ) (x : Fin n → ℤ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) :
    Prop :=
  s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 ∧
    ∃ (h₁ : (symIdx n (a % 2 = 1) s).card = a) (h₂ : (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a),
      HasVals Q₁ (nv (restr x _ h₁)) ∧ HasVals Q₂ (nv (restr x _ h₂))

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
