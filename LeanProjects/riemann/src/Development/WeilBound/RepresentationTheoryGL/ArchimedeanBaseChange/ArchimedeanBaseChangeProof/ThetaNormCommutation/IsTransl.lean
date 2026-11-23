import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev K2 (a b : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)

def geomSt2 (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
    kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)

def pol (c : TwCl (thE E n)) : E[X] := (c.rep * thE E n c.rep).val.charpoly

def geomRat2 (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (thE E a) × TwCl (thE E b), if pol c.1 ∈ Ell E a ∧ pol c.2 ∈ Ell E b then
    mass (thF E a) (ratF E a).range (ratF E a c.1.rep) * mass (thF E b) (ratF E b).range (ratF E b c.2.rep) *
      chW l₁ (pol c.1) * chW l₂ (pol c.2) *
      ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w c.1.rep, locEl b w c.2.rep) (φ w) else 0

def IsTestP (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : Prop :=
  ∃ (K₁ : ∀ w : Pl E, Subgroup (GLw a w)) (K₂ : ∀ w : Pl E, Subgroup (GLw b w)),
    IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) K₁ ∧ IsLevelFam (thL b) (fun w : Pl E => GlobalTheory.LFun.KGL w b) K₂ ∧
      GlobalTheory.BCT.IsTest (K2 a b) (fun w : Pl E => (K₁ w).prod (K₂ w)) φ

def G1 : Prop := USide

def G2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (l₁ : ∀ i, InfinitePlace E → DomWeight (a i))
    (l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)) (sg : ι → ℤˣ),
    (∀ i, a i ≤ n ∧ ∀ v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
      (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
      (φ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
      GlobalTheory.BCT.IsTest (KL n) K' f → (∀ a ≤ n, IsTestP (φ a) ∧ ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (φ a w)) →
      geomU S lam f = ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (φ (a i))

def G3 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ),
    IsTestP φ → (∃ w ∈ S, RegAt2 a b w (φ w)) →
    geomRat2 S l₁ l₂ φ = 2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * geomSt2 S l₁ l₂ φ

def IsTransl (u : GL (Fin n) E) : Prop := (∀ g, thE E n g = u * thetaE E n g * u⁻¹) ∧ u * thetaE E n u = 1

def cpt (w : Pl E) (u : GL (Fin n) E) (x : GA E n) : GLw n w := GeneralLinearGroup.map (cW w) (x * (ratGL E n u)⁻¹)

def cpt' (w : Pl E) (u : GL (Fin n) E) (x : GA E n) : GLw n w :=
  GeneralLinearGroup.map (cW w) (thetaGL n (conjAd E) (x * (ratGL E n u)⁻¹))

def adel (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (x : GA E a × GA E b) : ℂ :=
  (∏ v, ψ v (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2)) *
    ∏ᶠ w ∈ S, φ₁ w (cpt w u₁ x.1, cpt w u₂ x.2) * if IsSplitAt w then φ₂ w (cpt' w u₁ x.1, cpt' w u₂ x.2) else 1

def seen (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (y : GLw a w × GLw b w) : ℂ :=
  if IsSplitAt w then hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) else φ₁ w y

def EllC (d : GL (Fin n) ℂ) : Prop :=
  (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable ∧ ∀ z, (d * thetaR (starRingEnd ℂ) n d).val.charpoly.IsRoot z → ‖z‖ = 1

def LefAt [MeasurableSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)] (ν₁ : Measure (GL (Fin a) ℂ)) (ν₂ : Measure (GL (Fin b) ℂ))
    (l₁ : DomWeight a) (l₂ : DomWeight b) (val : ℂ) (ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) : Prop :=
  Continuous ψ ∧ HasCompactSupport ψ ∧ ∀ d₁ d₂, EllC d₁ → EllC d₂ →
    ∫ x, ψ (PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) a) x.1 d₁, PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) b) x.2 d₂) ∂(ν₁.prod ν₂) =
      val * starRingEnd ℂ (chAt l₁ (d₁ * thetaR (starRingEnd ℂ) a d₁).val.charpoly) *
        starRingEnd ℂ (chAt l₂ (d₂ * thetaR (starRingEnd ℂ) b d₂).val.charpoly)

def TranslEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ u : GL (Fin n) E, IsTransl u

def G4 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)]
  [BorelSpace (GA E b)] [MeasurableSpace (GL (Fin a) ℂ)] [BorelSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)]
  [BorelSpace (GL (Fin b) ℂ)] (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure]
  (ν₁ : Measure (GL (Fin a) ℂ)) [ν₁.IsHaarMeasure] (ν₂ : Measure (GL (Fin b) ℂ)) [ν₂.IsHaarMeasure], ∃ c : ℂ, c ≠ 0 ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
    ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (val : InfinitePlace E → ℂ)
      (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ),
      (∀ v, LefAt ν₁ ν₂ (l₁ v) (l₂ v) (val v) (ψ v)) → IsTestP φ₁ → IsTestP φ₂ →
      ellSum2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) = c * (∏ v, val v) * geomRat2 S l₁ l₂ (seen φ₁ φ₂)

end PositivityTheory.Rg.BcB.G8

end
