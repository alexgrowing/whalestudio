import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Tail

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def idem {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (U : Set (GLw a w × GLw b w)).indicator fun _ => ((U.relIndex (K2 a b w) : ℕ) : ℂ)

def IsLev (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) : Prop :=
  (∀ w, IsOpen (U w : Set (GLw a w × GLw b w)) ∧ U w ≤ K2 a b w) ∧ ∀ᶠ w in cofinite, U w = K2 a b w

def HasLev (G : H E a b → ℂ) : Prop :=
  ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ u ∈ U, ∀ x, G (x * finH u) = G x

def OfLev (S : Set (Pl E)) (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ) : Prop :=
  HasLev G ∧ ∀ w ∈ S, G ∈ fixed (pairRt a b w) (U₁ w) ∧ (IsSplitAt w → G ∈ fixed (pairRtT a b w) (U₂ w))

def actT (w : Pl E) (u : LF a b w) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRtT a b w m G z

def locM {k : Type} [Fintype k] (w : Pl E) (M : k → k → LF a b w) (G : k → H E a b → ℂ) : k → H E a b → ℂ :=
  fun x => ∑ y, actP w (M x y) (G y)

theorem matS_eq {n : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (X : Finset (GLw n w)) :
    matS h w μ f X = locM w fun x y : X => phiMu h w μ f x y := rfl

def DiagIdem {κ : Pl E → Type} (P : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (L : LM κ a b) : Prop :=
  ∀ w ∈ P, ∀ x y, L.m w x y = if x = y then idem (U w) else 0

def FmOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (w₀ : Pl E), IsLev U₁ → IsLev U₂ → L.Ok P → DiagIdem P U₁ L → (∀ i, OfLev S U₁ U₂ (F i)) → w₀ ∈ S →
    (w₀ ∉ P → (∀ w, w ≠ w₀ → L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actP w₀ (L.s w₀) (F i)) ∧
    (IsSplitAt w₀ → (∀ w, L.s w = idem (U₁ w)) → (∀ w, w ≠ w₀ → L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actT w₀ (L.t w₀) (F i))

def FmPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (m : ℕ), IsLev U₁ → IsLev U₂ → L.Ok P → (∀ w, L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
    (∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g) →
    (∀ i, OfLev S U₁ U₂ (F i)) → (convF B.ν (fm S P B e L))^[m] F ≠ 0 →
    ∀ w₀ : P, ∃ (α : A) (x : ∀ w : P, κ w), (locM w₀.1 (L.m w₀.1))^[m] (fun y => F (α, e.symm (Function.update x w₀ y))) ≠ 0

def ConvMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (A : Type)
  (ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (U : Subgroup (Hf E B.a B.b)) (F : A × B.κ → H E B.a B.b → ℂ), IsFinM ψ → IsFinM ψ' →
  IsOpen (U : Set (Hf E B.a B.b)) → (∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) →
    convF B.ν (mulF B.ν ψ ψ') F = convF B.ν ψ (convF B.ν ψ' F) ∧
      ((∀ x y, ∀ u ∈ U, ∀ h, ψ' x y (u * h) = ψ' x y h) → ∀ i, ∀ u ∈ U, ∀ x, convF B.ν ψ' F i (x * finH u) = convF B.ν ψ' F i x)

def LocPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (k : Type) [Fintype k]
  (U : Subgroup (GLw a w × GLw b w)) (G : k → H E a b → ℂ) (m : ℕ), IsOpen (U : Set (GLw a w × GLw b w)) →
  (∀ y, G y ∈ fixed (pairRt a b w) U) →
  (∀ (c : ℂ) (M : k → k → LF a b w), (locM w fun x y => c • M x y)^[m] G ≠ 0 → (locM w M)^[m] G ≠ 0) ∧
    ∀ q : k → LF a b w, (locM w fun x y => if x = y then q x else 0)^[m] G ≠ 0 → ∃ x, (actP w (q x))^[m] (G x) ≠ 0

def ActHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f : LF a b w) (G : H E a b → ℂ),
  HasCompactSupport f → (∀ k ∈ K2 a b w, ∀ g, f (g * k) = f g) →
  (G ∈ fixed (pairRt a b w) (K2 a b w) → actP w f G = GlobalTheory.LFun.heckeVec (pairRt a b w) (K2 a b w) f G) ∧
    (G ∈ fixed (pairRtT a b w) (K2 a b w) → actT w f G = GlobalTheory.LFun.heckeVec (pairRtT a b w) (K2 a b w) f G)

def RFmOne : Prop := IntHint → Slots → FmOne
def RFmPow : Prop := IntHint → Slots → FmPow

end PositivityTheory.Rg.BcB.F.Tail

end
