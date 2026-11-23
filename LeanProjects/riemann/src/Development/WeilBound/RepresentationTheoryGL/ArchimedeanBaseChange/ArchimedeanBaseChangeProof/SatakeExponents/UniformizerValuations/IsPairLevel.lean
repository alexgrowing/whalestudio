import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

def SecEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S₀ : Finset (Pl E)), S₀.card ≤ 1 →
  ∃ Sec : Set (Pl E), IsSection Sec ∧ (∀ w ∈ S₀, w ∈ Sec) ∧ ∀ w, ¬ IsSplitAt w → w ∈ Sec

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e ∧ (∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) ∧ (∀ᶠ w : Pl E in cofinite, μ.UnrAt w) ∧
    ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)

def UnifEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E,
  ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ ∧ IsUnifV E w (ϖ : w.adicCompletion E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsPairLevel {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : Prop :=
  ∃ L₁ L₂, L = Subgroup.prod L₁ L₂ ∧ GlobalTheory.BCT.IsLevel (thL a w) (KGL w a) L₁ ∧ GlobalTheory.BCT.IsLevel (thL b w) (KGL w b) L₂

def BadEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ), a ≤ n → ∀ (w : Pl E)
  (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) → ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ (L : Subgroup (GLw a w × GLw (n - a) w)) (φ : LF a (n - a) w), IsPairLevel L ∧ IsHecke L φ ∧
      Match n a (n - a) w μ (U.lone KB) φ

def SplitEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) → ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ) (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)),
      K'.subgroupOf (UL n w) = KB ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w n ∧
      (∀ k ∈ KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w n) ∧ (∀ k ∈ KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1

def KEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Sec : Set (Pl E)), IsSection Sec →
  ∀ R : Finset (Pl E), (∀ w ∈ R, w ∈ Sec) → ∀ μ : ∀ w : Pl E, (w.adicCompletion E)ˣ →* ℂˣ,
  (∀ w, IsOpen ((μ w).ker : Set (w.adicCompletion E)ˣ)) → ∀ L : ∀ (a : ℕ) (w : Pl E), Subgroup (GLw a w × GLw (n - a) w),
  (∀ a ≤ n, ∀ w ∈ R, IsPairLevel (L a w)) →
    ∃ K : ∀ w : Pl E, Subgroup (GLw n w), F5.IsLevel K ∧ (∀ w, IsCompact (K w : Set (GLw n w))) ∧
      (∀ w : Pl E, (∀ u ∈ R, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) → K w = KGL w n) ∧
      (∀ a (ha : a ≤ n), ∀ w ∈ R, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
        m ∈ L a w ∧ μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1) ∧
      ∀ a (ha : a ≤ n), ∀ w ∈ R, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
        μ u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
          ∃ m' ∈ L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2

end PositivityTheory.Rg.BcB.F.Ex0

end
