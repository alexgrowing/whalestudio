import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.HermInf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def TMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (κ : Pl E → Type) [∀ w, Fintype (κ w)] (P : Finset (Pl E)),
  (∀ w, Nonempty (κ w)) → ∀ L L' : LM κ a b, L.Ok P → L'.Ok P → (L.mul L').Ok P

def TTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (κ : Pl E → Type) [∀ w, Fintype (κ w)] (P : Finset (Pl E)),
  (∀ w, Nonempty (κ w)) → ∀ (L : LM κ a b) (N : ∀ w, κ w → κ w → ℂ), L.Ok P → IsTestP (L.tr P N)

def TSeen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (φ₁ φ₂ : ∀ w : Pl E, LF a b w), IsTestP φ₁ → IsTestP φ₂ → IsTestP (seen φ₁ φ₂)

def GuHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → MLM.MOk d →
  (∀ w, IsLevel (MonoidHom.id _) (KL n w) (d.KU w)) → ∀ w ∈ d.B, IsHecke (d.KU w) (d.g₀ w) ∧ ∀ m, IsHecke (d.KU w) (d.gU m w)

def HuHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ w, d.Good w → ∀ k, IsHecke (KL n w) (d.hU w k)

def PsiGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E)
  (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S → ∀ (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E)
  (L₀ : LM κ B.a B.b) (t₀ : PT B), L₀.Ok P → (L₀.mul L₀).Eqv P L₀ → t₀.ψ = rt u₁ u₂ (fm S P B e L₀) →
  ∀ l : List (BGen B × LM κ B.a B.b), (∀ x ∈ l, x.2.Ok P ∧ (L₀.mul x.2).Eqv P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = L₀) ∨ ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm S P B e x.2)) →
    (BGen.wd (l.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀))

def ChainSc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E) (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n)
  (C : Chain μ e lam) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → GlobalTheory.BCT.IsTest (KL n) K' f →
    ∀ (u₁ : ∀ a, GL (Fin a) E) (u₂ : ∀ a, GL (Fin (n - a)) E), (∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)) →
    ∀ (φ₁ φ₂ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ),
    (∀ a ≤ n, IsTestP (φ₁ a) ∧ IsTestP (φ₂ a) ∧ IsTestP (seen (φ₁ a) (φ₂ a)) ∧
      ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (seen (φ₁ a) (φ₂ a) w)) →
    (∀ i, ∃ w ∈ S, RegAt2 (C.a i) (n - C.a i) w (seen (φ₁ (C.a i)) (φ₂ (C.a i)) w)) →
    ∀ (val : C.ι → InfinitePlace E → ℂ) (ψ : ∀ i, InfinitePlace E → GL (Fin (C.a i)) ℂ × GL (Fin (n - C.a i)) ℂ → ℂ),
    (∀ i v, LefAt (C.νC (C.a i)) (C.νC (n - C.a i)) (C.l₁ i v) (C.l₂ i v) (val i v) (ψ i v)) → ∀ (s : C.ι → ℂ) (z : ℂ),
    (∀ i, s i * ∏ v, val i v = z) →
    z * geomU S lam f = ∑ i, C.c i * (s i *
      ellSum2 (C.μG (C.a i)) (C.μG (n - C.a i)) (adel S (u₁ (C.a i)) (u₂ (C.a i)) (ψ i) (φ₁ (C.a i)) (φ₂ (C.a i))))

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
