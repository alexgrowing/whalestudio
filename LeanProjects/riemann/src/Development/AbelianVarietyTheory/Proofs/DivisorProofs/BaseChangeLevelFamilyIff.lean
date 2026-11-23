import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def tens {G H : Type} (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun y => f y.1 * g y.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def geomSt2 (a b : ℕ) (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
    kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)

def spec2 {a b : ℕ} {ι : Type} [Fintype ι] (S : Set (Pl E)) (t₁ : ι → Term E a) (t₂ : ι → Term E b) (C : ι → ℂ)
    (K₁ : ∀ w : Pl E, Subgroup (GLw a w)) (K₂ : ∀ w : Pl E, Subgroup (GLw b w))
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ i, C i * ∏ᶠ w ∈ S, twTr (extT ((t₁ i).rep w) ((t₂ i).rep w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
    ((K₁ w).prod (K₂ w)) (φ w) (TensorProduct.map ((t₁ i).A w) ((t₂ i).A w))

end GlobalTheory.BCT
