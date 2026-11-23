import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.InstIPSFB

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

def FrameBoundModuleCondition : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S), MLM.MOk F₀.d₀

def FrameEx0 : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (Pl E), S.card ≤ 1 → Nonempty (Frame0 hR π S)

def FrameEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T : Finset (Pl E)),
    Nonempty (RunFrame F₀ T)

def FrameOk : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct

def FrameBound : Prop := ∀ (hR : Rd.ReadLimit) (hD : DiagAlg) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T)
    (h : F.Struct), (F.toGenIn hD h).Bound

def FrameRead : Prop := ∀ (hR : Rd.ReadLimit) (hD : DiagAlg) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T)
    (h : F.Struct), (F.toGenIn hD h).Read

theorem genEx_of (hR : Rd.ReadLimit) (hD : DiagAlg) (h0 : FrameEx0) (h1 : FrameEx) (h2 : FrameOk) (h3 : FrameBound)
    (h4 : FrameRead) : GenEx := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨F₀⟩ := h0 hR E hE n hn π hπ S hS
  refine ⟨F₀.K, F₀.W, F₀.hK, F₀.hW, fun T => ?_⟩
  obtain ⟨F⟩ := h1 hR E hE n hn π hπ S F₀ T
  have h := h2 hR E hE n hn π S T F₀ F
  exact ⟨F.toGenIn hD h, h3 hR hD E hE n hn π hπ S T F₀ F h, h4 hR hD E hE n hn π hπ S T F₀ F h⟩

end PositivityTheory.Rg.BcB.F

end
