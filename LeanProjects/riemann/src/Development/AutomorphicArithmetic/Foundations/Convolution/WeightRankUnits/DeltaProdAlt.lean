import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.ConvolutionTheory.G2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def phase (e : InfinitePlace E → ℤ) (R : E) (v : InfinitePlace E) : ℂ :=
  (v.embedding R / (‖v.embedding R‖ : ℂ)) ^ e v * ‖v.embedding R‖

def unit2 (a b : ℕ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)).indicator 1

def muAt (μ : HChar E) (w : Pl E) (x : E) : ℂ :=
  if h : algebraMap E (w.adicCompletion E) x ≠ 0 then (μ.loc w (Units.mk0 _ h) : ℂ) else 0

def EllCsr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
  P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse ∧
    ∀ w : Pl E, IsCsr w (atPl w P)

def RealProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → ∀ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → InfinitePlace E → DomWeight a)
    (l₂ : ι → InfinitePlace E → DomWeight b) (sg : ι → ℤˣ),
    (∀ i v, (infOfWeight (l₁ i v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ i v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
      infOfWeight (lam v)) ∧
    ∀ P₁ P₂ : E[X], P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
      (∏ v, phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂) = ∑ i, ((sg i : ℤ) : ℂ) * chW (l₁ i) P₁ * chW (l₂ i) P₂

def DeltaLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ → ∀ w : Pl E,
    delta w (μ.loc w) (atPl w P₁) (atPl w P₂) =
      ∏ᶠ u ∈ {u : Pl E | u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))},
        muAt μ u (resultant P₁ P₂) * absHalf u (algebraMap E (u.adicCompletion E) (resultant P₁ P₂))

def MuProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ R : E, R ≠ 0 →
  (Function.mulSupport fun u : Pl E => muAt μ u R).Finite ∧
    (∏ᶠ u : Pl E, muAt μ u R) * ∏ v : InfinitePlace E, (v.embedding R / (‖v.embedding R‖ : ℂ)) ^ e v = 1

def AbsProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (R : E), R ≠ 0 →
  (Function.mulSupport fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) R)).Finite ∧
    (∏ᶠ u : Pl E, absHalf u (algebraMap E (u.adicCompletion E) R)) * ∏ v : InfinitePlace E, (‖v.embedding R‖ : ℂ) = 1

def Regroup : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ g : Pl E → ℂ, (Function.mulSupport g).Finite →
  let G : Pl E → ℂ := fun w => ∏ᶠ u ∈ {u : Pl E | u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, g u
  (Function.mulSupport G).Finite ∧ ∏ᶠ w ∈ S, G w = ∏ᶠ u, g u

def DeltaProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S →
  ∀ (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
    (Function.mulSupport fun w : Pl E => delta w (μ.loc w) (atPl w P₁) (atPl w P₂)).Finite ∧
      (∏ᶠ w ∈ S, delta w (μ.loc w) (atPl w P₁) (atPl w P₂)) * ∏ v, phase e (resultant P₁ P₂) v = 1

def StOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (Q : (w.adicCompletionIntegers E)[X]), Q.Monic → Q.natDegree = n →
  Q.Separable → IsUnit (Q.coeff 0) → (2 : 𝓞 E) ∉ w.asIdeal →
  (IsSplitAt w ∨ ∃ δ : GLw n w, (nrmL n w δ).val.charpoly = Q.map (algebraMap _ (w.adicCompletion E))) →
    stTw n w (Q.map (algebraMap _ (w.adicCompletion E))) ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = 1

def StTens : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
  stTw2 a b w Q₁ Q₂ (unit2 a b w) =
    stTw a w Q₁ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w b : Set (GLw b w)).indicator 1)

def StAA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b →
  ∀ᶠ w : Pl E in cofinite, stTw2 a b w (atPl w P₁) (atPl w P₂) (unit2 a b w) = 1

def FinP : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, HasCompactSupport (φ w)) → (∀ᶠ w in cofinite, φ w = unit2 a b w) →
    {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w) ≠ 0}.Finite

def TermId : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S →
  ∀ (n a b : ℕ) (f : ∀ w : Pl E, UL n w → ℂ) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), (∀ᶠ w in cofinite, φ w = unit2 a b w) →
    (∀ w ∈ S, Match n a b w (μ.loc w) (f w) (φ w)) → ∀ P₁ P₂ : E[X], P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
    (S ∩ Function.mulSupport fun w => stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w)).Finite ∧
      ∏ᶠ w ∈ S, kapOrb n w (atPl w P₁) (atPl w P₂) (f w) =
        (∏ v, phase e (resultant P₁ P₂) v) * ∏ᶠ w ∈ S, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w)

end UpperTheory.ConvolutionTheory.G2
