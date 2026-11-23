import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FrameExOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def ExTb : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T : Finset (Pl E)),
  ∃ (T' : Finset (Pl E)) (b : ∀ w : Pl E, GLw n w), T'.Nonempty ∧
    (∀ w ∈ T', w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ IsUnramU π w ∧ IsWitt n w (b w) ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) ∧
    (∀ w, w ∉ T' → b w = F₀.d₀.b w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → w ∈ T'

def ExTbOf : Prop := Inert.InertPlaceEx → Inert.WittEx → InertInSec → ExTb

def ExCEM : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E))
  (b : ∀ w : Pl E, GLw n w) (ξ : Pl E → Fin n → ℂˣ), (∀ w ∈ T', ¬ IsSplitAt w ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) →
  ∃ (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ) (m : ℕ), 1 ≤ m ∧
    (∀ w ∈ T', (↑(c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2) ∧ (∀ w ∈ T', evalGL (c w) (chiN w (ξ w)) = 1) ∧
    (∀ w, w ∉ T' → c w = F₀.d₀.c w) ∧ (∀ w, w ∉ F₀.d₀.S₀ → e w = F₀.d₀.e w) ∧
    (∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → ∀ w ∈ T', ∀ s (h : LocData.admitted n (F₀.C.a i) s)
      (ex : Fin (F₀.C.a i) ⊕ Fin (n - F₀.C.a i) ≃ Fin n) he ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb →
      ((c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s) *
        ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0 →
      Choice.chiOf w (Choice.shufOf w n (F₀.C.a i) s h ex he ((-1) ^ (n - F₀.C.a i)) ((-1) ^ F₀.C.a i)) ξa ξb = chiN w (ξ w)) ∧
    (∀ w ∈ F₀.d₀.S₀, PositivityTheory.Rg.BcN.F2.IsHk (F₀.d₀.K' w) (e w)) ∧
    (∀ w ∈ F₀.d₀.S₀, ∃ P : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ ∧
      (∃ v₀ ∈ fixed P.ρ (F₀.d₀.K' w), ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧
        ∀ v ∈ fixed P.ρ (F₀.d₀.K' w), PositivityTheory.Rg.BcN.F2.hk P.ρ (F₀.d₀.K' w) (e w) v =
          ((((F₀.d₀.K' w).relIndex (GlobalTheory.LFun.KGL w n) : ℕ) : ℂ) * l v) • v₀) ∧
      ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → ∀ τ : SmIrr (GLw n w),
        GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
          ∀ y ∈ fixed τ.ρ (F₀.d₀.K' w), PositivityTheory.Rg.BcN.F2.hk τ.ρ (F₀.d₀.K' w) (e w) y = 0) ∧
    RF_choiceM F₀ (F₀.loc T' c e b) m

def CompFixS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ w : Pl E, IsSplitAt w → ∀ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) → IsCompact (K' : Set (GLw n w)) →
    (∃ φ ∈ π, φ ≠ 0 ∧ ∀ x ∈ locU n w, cLoc w x ∈ K' → RU E n x φ = φ) →
    ∃ P : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ ∧ ∃ v ∈ fixed P.ρ K', v ≠ 0

def ExCEMOf : Prop := CompFixS → CandIndep → CandFin → FixFin → Choice.ChoiceT → Choice.ChoiceS → Choice.ChoiceM → Choice.ShufEx →
  Choice.VResStd → Choice.ChiEval → ExCEM

end PositivityTheory.Rg.BcB.F.FX

end
