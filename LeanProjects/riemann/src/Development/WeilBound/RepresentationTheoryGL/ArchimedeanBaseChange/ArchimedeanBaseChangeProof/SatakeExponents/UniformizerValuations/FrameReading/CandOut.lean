import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem allLeaves_imp {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, hp => h _ V hp
  | _, .node t₁ t₂, hp => ⟨allLeaves_imp h t₁ hp.1, allLeaves_imp h t₂ hp.2⟩

set_option maxHeartbeats 2000000 in

def CandTOut : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    (∀ τ lam, HasWeightAt π τ lam → ∑ k, D.m k τ = infOfWeight lam) →
    (∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w) →
    TOut π S T F₀.K F₀.W D

def CandS : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w ∈ S, IsSplitAt w → ∃ P : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def CandT : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def CandLev : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (F₀.K w)

theorem candTOut_of (hS : CandS) (hT : CandT) (hL : CandLev) : CandTOut := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne hwt hgood
  refine tout_of hwt hgood (hS hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne)
    (hT hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne) (hL hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne)
    (F₀.W_join i s₁ s₂ Pa Pb D hc.ctx ?_ ?_)
  · exact allLeaves_imp (fun _ _ h => h.imp_right fun ⟨K', _, W', hW', h'⟩ => ⟨K', W', hW', h'⟩) _ hc.leaves₁
  · exact allLeaves_imp (fun _ _ h => h.imp_right fun ⟨K', _, W', hW', h'⟩ => ⟨K', W', hW', h'⟩) _ hc.leaves₂

end PositivityTheory.Rg.BcB.F

end
