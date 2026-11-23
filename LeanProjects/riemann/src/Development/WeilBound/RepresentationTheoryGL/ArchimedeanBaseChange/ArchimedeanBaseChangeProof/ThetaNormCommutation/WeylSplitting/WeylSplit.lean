import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.G2

def dInf {E : Type} [Field E] [NumberField E] (e : InfinitePlace E → ℤ) (R : E) : ℂ :=
  ∏ v : InfinitePlace E, (starRingEnd ℂ (v.embedding R) / (‖v.embedding R‖ : ℂ)) ^ e v / (‖v.embedding R‖ : ℂ)

def ProdDelta : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E)
  (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ (a b : ℕ) (p₁ p₂ : E[X]), p₁ ∈ Ell E a →
    p₂ ∈ Ell E b → IsCoprime p₁ p₂ →
      (Function.mulSupport fun w : Pl E => delta w (μ.loc w) (atPl w p₁) (atPl w p₂)).Finite ∧
      ∏ᶠ w ∈ S, delta w (μ.loc w) (atPl w p₁) (atPl w p₂) = dInf e (resultant p₁ p₂)

def WeylSplit : Prop := ∀ (n a : ℕ), a ≤ n → ∀ e : ℤ, Odd e → ∀ lam : DomWeight n,
  ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight (n - a)) (sg : ι → ℤˣ),
    (∀ i, (infOfWeight (l₁ i)).map (· + ((n - a : ℕ) : ℂ) * (e : ℂ) / 2) +
      (infOfWeight (l₂ i)).map (· + (a : ℂ) * (e : ℂ) / 2) = infOfWeight lam) ∧
    ∀ p₁ p₂ : ℂ[X], p₁.Monic → p₂.Monic → p₁.natDegree = a → p₂.natDegree = n - a → (p₁ * p₂).Separable →
      (∀ z ∈ (p₁ * p₂).roots, ‖z‖ = 1) →
      starRingEnd ℂ (chAt lam (p₁ * p₂)) =
        (starRingEnd ℂ (resultant p₁ p₂) / (‖resultant p₁ p₂‖ : ℂ)) ^ e / (‖resultant p₁ p₂‖ : ℂ) *
          ∑ i, ((sg i : ℤ) : ℂ) * starRingEnd ℂ (chAt (l₁ i) p₁) * starRingEnd ℂ (chAt (l₂ i) p₂)

def KapMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (P₁ P₂ : E[X]),
  P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ → kap (P₁ * P₂) = kap P₁ * kap P₂

def KapOrbAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
  ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), GlobalTheory.BCT.IsTest (KL n) K' f →
  ∀ p₁ p₂ : E[X], p₁ ∈ Ell E p₁.natDegree → p₂ ∈ Ell E p₂.natDegree → IsCoprime p₁ p₂ → p₁.natDegree + p₂.natDegree = n →
    (Function.mulSupport fun w : Pl E => kapOrb n w (atPl w p₁) (atPl w p₂) (f w)).Finite

def EllLocal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (p₁ p₂ : E[X]), p₁ ∈ Ell E a →
  p₂ ∈ Ell E b → IsCoprime p₁ p₂ → ∀ w : Pl E, (atPl w p₁).Monic ∧ (atPl w p₂).Monic ∧ (atPl w p₁).natDegree = a ∧
    (atPl w p₂).natDegree = b ∧ (atPl w p₁ * atPl w p₂).Separable ∧ IsCsr w (atPl w p₁) ∧ IsCsr w (atPl w p₂)

def ChWMap : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (P : E[X]),
  chW lam P = ∏ v : InfinitePlace E, starRingEnd ℂ (chAt (lam v) (P.map v.embedding))

end PositivityTheory.Rg.BcB.G8.G2

end
