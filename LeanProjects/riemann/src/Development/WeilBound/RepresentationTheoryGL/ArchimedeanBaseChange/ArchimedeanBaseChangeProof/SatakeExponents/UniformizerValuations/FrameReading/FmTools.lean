import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def actS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : Slot S → (H E a b → ℂ) → H E a b → ℂ
  | .inl w => actP w.1 (φ₁ w.1)
  | .inr w => actT w.1 (φ₂ w.1)

def FinAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁ → IsTestP φ₂ → ∀ G : H E B.a B.b → ℂ, HasLev G →
  ∀ l : List (Slot S), l.Nodup → (∀ i ∉ l, actS φ₁ φ₂ i G = G) →
    ∀ x, ∫ h, finFn S φ₁ φ₂ h * G (x * finH h) ∂B.ν = B.vol * l.foldr (fun i g => actS φ₁ φ₂ i g) G x

def ActAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ → IsTestP ψ₁ → IsTestP ψ₂ →
  ∀ G G' : H E a b → ℂ, HasLev G → HasLev G' → ∀ i j : Slot S,
    HasLev (actS φ₁ φ₂ i G) ∧ (∀ c : ℂ, actS φ₁ φ₂ i (G + c • G') = actS φ₁ φ₂ i G + c • actS φ₁ φ₂ i G') ∧
    (i ≠ j → actS φ₁ φ₂ i (actS ψ₁ ψ₂ j G) = actS ψ₁ ψ₂ j (actS φ₁ φ₂ i G)) ∧
    actS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i G =
      actS φ₁ φ₂ i (actS ψ₁ ψ₂ i G)

def ActIdem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
  (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ), IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ K2 a b w → HasLev G →
  (actP w (idem L) G = G ↔ G ∈ fixed (pairRt a b w) L) ∧
  (actT w (idem L) G = G ↔ G ∈ fixed (pairRtT a b w) L)

section

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)

def Quiet {A : Type} (L : LM κ B.a B.b) (i₀ : Slot S) (F : A × B.κ → H E B.a B.b → ℂ) : Prop :=
  (∀ w ∈ P, (∀ h : w ∈ S, i₀ ≠ Sum.inl ⟨w, h⟩) → ∀ x y, x ≠ y → L.m w x y = 0) ∧
    ∀ i : Slot S, i ≠ i₀ → ∀ p x y, (∀ w : P, (∀ h : w.1 ∈ S, i₀ ≠ Sum.inl ⟨w.1, h⟩) → e x w = e y w) →
      actS (L.ent P (e x) (e y)) L.t i (F (p, y)) = F (p, y)

end

def FmAtP : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)]
  (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → ∀ hP : (↑P : Set (Pl E)) ⊆ S,
  ∀ (A : Type) (L : LM κ B.a B.b) (w₀ : P) (F : A × B.κ → H E B.a B.b → ℂ), L.Ok P → (∀ i, HasLev (F i)) →
    Quiet S P B e L (Sum.inl ⟨w₀.1, hP w₀.2⟩) F → ∀ p x,
    convF B.ν (fm S P B e L) F (p, x) =
      ∑ y : κ w₀, actP w₀.1 (L.m w₀ (e x w₀) y) (F (p, e.symm (Function.update (e x) w₀ y)))

def FmOff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)]
  (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (A : Type) (L : LM κ B.a B.b) (i₀ : Slot S) (F : A × B.κ → H E B.a B.b → ℂ), L.Ok P → (∀ i, HasLev (F i)) →
    (∀ w ∈ P, ∀ h : w ∈ S, i₀ ≠ Sum.inl ⟨w, h⟩) → Quiet S P B e L i₀ F → ∀ p x,
    convF B.ν (fm S P B e L) F (p, x) = actS L.s L.t i₀ (F (p, x))

def FinActOf : Prop := IntHint → Slots → FinConv → ActAlg → FinAct

def FmAtPOf : Prop := FinConv → FinAct → FmAtP

def FmOffOf : Prop := FinConv → FinAct → FmOff

def FmOneOf : Prop := FmOff → ActIdem → FmOne

def FmPowOf : Prop := FmAlg → FmAtP → Tail.ConvMul → ActAlg → ActIdem → FmPow

end PositivityTheory.Rg.BcB.F.FA

end
