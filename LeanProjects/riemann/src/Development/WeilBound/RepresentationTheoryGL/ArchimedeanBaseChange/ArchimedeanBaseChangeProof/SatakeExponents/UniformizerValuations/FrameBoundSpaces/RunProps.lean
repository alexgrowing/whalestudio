import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RF_same {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  d.S₀ = F₀.d₀.S₀ ∧ d.Bad = F₀.d₀.Bad ∧ d.μ = F₀.d₀.μ ∧ d.ϖ = F₀.d₀.ϖ ∧ d.K' = F₀.d₀.K' ∧ d.X = F₀.d₀.X ∧
  d.L = F₀.d₀.L ∧ d.fix = F₀.d₀.fix ∧ d.KB = F₀.d₀.KB

def RF_T_in {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ w ∈ d.T, w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ IsUnramU π w ∧ IsWitt n w (d.b w)

def RF_choiceT {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ d.T, ∀ s (h : LocData.admitted n (F₀.C.a i) s) ξa ξb,
  JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb →
  ((d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0 →
  N3.Mono ξa ∧ N3.Mono ξb ∧ ∀ (ϖ : w.adicCompletion E) (q : ℕ), IsUnramInv ϖ (cj w) q →
    ∀ α, HasSatAt π w (cj w) ϖ q α →
      (Finset.univ.val.map ξa).map (· * (F₀.μ ^ (n - F₀.C.a i)).val w) + (Finset.univ.val.map ξb).map (· * (F₀.μ ^ F₀.C.a i).val w) =
        GlobalTheory.LGrp.bcParam n α

def RF_choiceS {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ w ∈ F₀.d₀.S₀, ∃ P : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ ∧
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ τ : SmIrr (GLw n w),
    GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) → ∀ y ∈ fixed τ.ρ (F₀.d₀.K' w), hk τ.ρ (F₀.d₀.K' w) (d.e w) y = 0

def RF_choiceM {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (m : ℕ) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
  (∀ w ∈ F₀.d₀.S₀, Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) < m) ∧
    ∀ w ∈ d.T, Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m

end PositivityTheory.Rg.BcB.F

end
