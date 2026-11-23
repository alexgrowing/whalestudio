import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LevIdem
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LevRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (d : LocData E n) (a : ℕ),
  a ≤ n → IsSection S → d.Ok → (↑d.P : Set (Pl E)) ⊆ S → IsLev (d.lev a) ∧ IsLev (d.lev₂ a) ∧
  ∀ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E (n - a) → ℂ)) (G : H E a (n - a) → ℂ),
    TypeH (lev₁ S d a) (lev₂ S d a) W₁ W₂ G → OfLev S (d.lev a) (d.lev₂ a) G

set_option maxHeartbeats 1000000 in

def FRGood : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (i : F₀.C.ι)
  (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n),
  Ctx F₀.μ s₁ s₂ Pa Pb D → ∀ (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ), G ≠ 0 →
  (∀ j, G j ∈ pairSpace s₁.space s₂.space) → (∀ j, OfLev F₀.Sec (F.d.lev _) (F.d.lev₂ _) (G j)) →
  (∀ x : {w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool,
    convF (F.B i).ν (F.ψ i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) G = (F.ug (.inr (.inr x))).p F.fam F.i₀ • G) →
  ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w

set_option maxHeartbeats 1000000 in

def FRWeight : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
  (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n),
  F₀.Cand d i s₁ s₂ Pa Pb D → ∀ τ lam, HasWeightAt π τ lam → ∑ j, D.m j τ = infOfWeight lam

def LevReadOf : Prop := LevIdem → LevRead

def FRGoodOf : Prop := GoodL → LevRead → FRGood

def FRWeightOf : Prop := WeightL → FRWeight

end PositivityTheory.Rg.BcB.F.FG

end
