import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def CandIndep : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E))
  (c c' : Pl E → (Fin n → ℤ) →₀ ℂ) (e e' : ∀ w : Pl E, GLw n w → ℂ) (b b' : ∀ w : Pl E, GLw n w) i s₁ s₂ Pa Pb D,
  F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D ↔ F₀.Cand (F₀.loc T' c' e' b') i s₁ s₂ Pa Pb D

def CandFin : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ),
  1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E))
  (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ) (b : ∀ w : Pl E, GLw n w),
  (∀ w ∈ T', ¬ IsSplitAt w ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) →
  (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
    ∀ s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → w ∈ T' →
      ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
  (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D →
    ∃ j, (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (Dl j) w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) = Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))) ∧
  ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → ∀ w ∈ T',
    Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m₀

end PositivityTheory.Rg.BcB.F.FX

end
