import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ConjFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  (∀ (w u : Pl E) (G : H E a b → ℂ), IsSplitAt w → ConjPl w u → G ∈ fixed (pairRtT a b w) (K2 a b w) →
    G ∈ fixed (pairRt a b u) (K2 a b u)) ∧
  ∀ S : Set (Pl E), IsSection S → (∀ u, IsSplitAt u → u ∈ S ∨ ∃ w ∈ S, IsSplitAt w ∧ ConjPl w u) ∧
    ∀ X : Finset (Pl E), {u | ∃ w ∈ X, ConjPl w u}.Finite

def USat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E)
  (σ : SmIrr (UL n w)), IsSplitAt w → IsCompU π w σ → fixed σ.ρ (KL n w) ≠ ⊥ →
  ∃ B, SatAtU π w B ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    twTr σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id = satEig (qV E w) n B k

def CtHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ), IsSplitAt w → IsUnifV E w ϖ →
  (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → ν u = 1) →
  HasCompactSupport (ctT h w ν ϖ k) ∧ (∀ y ∈ K2 a b w, ∀ g, ctT h w ν ϖ k (g * y) = ctT h w ν ϖ k g) ∧ ν ((-1) ^ (a * b)) = 1

def USatOf : Prop := SplitDict → USat

end PositivityTheory.Rg.BcB.F.FG

end
