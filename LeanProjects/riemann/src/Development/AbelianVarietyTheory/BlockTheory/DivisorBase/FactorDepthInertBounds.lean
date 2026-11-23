import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∉ w.asIdeal ^ 2

def quadK (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {(H.rt : E)}

def InertK (H : Host E) (p : ℕ) : Prop := (Ideal.span {(p : 𝓞 (quadK H))}).IsPrime

def SplitK (H : Host E) (p : ℕ) : Prop :=
  ∃ P Q : Ideal (𝓞 (quadK H)), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ P * Q = Ideal.span {(p : 𝓞 (quadK H))}

def boundAll (p i k : ℕ) : ℝ := (i : ℝ) * k / ((p : ℝ) - 1)

def boundInert (p j' i k : ℕ) : ℝ := 2 * (i : ℝ) * k / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * (j' : ℝ) * k / ((p : ℝ) - 1)

def boundSplit (p j' k : ℕ) : ℝ := (k : ℝ) * j' / ((p : ℝ) - 1)

def upperInert (p N j' k : ℕ) : ℝ :=
  (k : ℝ) * ((j' : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j') * p / ((p : ℝ) ^ 2 - 1))

def lowerInert (p i k cr : ℕ) : ℝ :=
  (i : ℝ) * k * p / ((p : ℝ) ^ 2 - 1) - (k : ℝ) * cr * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p k + 1)

def boundFine (p N j' i k : ℕ) : ℝ :=
  (k : ℝ) * ((N : ℝ) - 2 * j' - i) * p / ((p : ℝ) ^ 2 - 1) +
    (k : ℝ) * j' * (3 + 1 / 2 * Real.logb p k) / ((p : ℝ) - 1) + (i : ℝ) ^ 2 * (Real.logb p k + 1)

variable {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
  {p : ℕ} [Fact p.Prime]

def AtEvery (la : PointsOfFlagModel.abelian₂ p c) (Q : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, Q T io y

def kap {T : CDVR} (X : ValExt T p) (i k : ℕ) : EReal := content (vX_vp X) (detPow X.C i k)

variable {Xo c} in

def htColength {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)
    (f : Lt1 Dw) : EReal :=
  ⨅ (lv : Fin (rk f) → Fin (chD Ch.ch) → X.C) (_ : ∀ b, IsCharLog (fgl Ch X) (lv b)),
    toE (vX_vp X (Matrix.det (Matrix.of fun a b : Fin (rk f) => ∑ e, lv b e * frame Ch X f a e)))

def OscLe (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (b : ℝ) : Prop :=
  AtEvery Xo c la fun _ _ y => AtEvery Xo c la fun _ _ η => nuFac p y f k ≤ nuFac p η f k + (b : EReal)

def ClauseAll (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T _ y => 0 ≤ nuFac p y f k ∧ ∀ X : ValExt T p,
    nuFac p y f k ≤ kap X (rk f) k ∧ kap X (rk f) k ≤ (boundAll p (rk f) k : EReal)) ∧
  OscLe Xo c la f k (boundAll p (rk f) k)

def ClauseInert (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T _ y => ∀ X : ValExt T p,
    kap X (rk f) k ≤ nuFac p y f k + (boundInert p Dw.q (rk f) k : EReal)) ∧
  OscLe Xo c la f k (boundInert p Dw.q (rk f) k)

def ClauseSplit (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T io y =>
    (∀ (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      nuFacC Ch X f k ≤ ((k : ℝ) : EReal) * htColength Ch X f ∧
        htColength Ch X f ≤ (boundSplit p Dw.q 1 : EReal)) ∧
    nuFac p y f k ≤ (boundSplit p Dw.q k : EReal)) ∧
  OscLe Xo c la f k (boundSplit p Dw.q k)

def ClauseFine (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun _ _ η => ∃ cr : ℕ, cr ≤ rk f ∧ (cr : ℝ) ≤ (Dw.q : ℝ) * (3 / 2 + 1 / 2 * Real.logb p k) ∧
    (lowerInert p (rk f) k cr : EReal) ≤ nuFac p η f k) ∧
  (AtEvery Xo c la fun _ _ y => nuFac p y f k ≤ (upperInert p (Dw.p + Dw.q) Dw.q k : EReal)) ∧
  OscLe Xo c la f k (boundFine p (Dw.p + Dw.q) Dw.q (rk f) k)

def FactorBoundsAt (p : ℕ) [Fact p.Prime] : Prop :=
  UnramIn E p → ∀ (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ),
    ClauseAll Xo c la f k ∧
    (InPsi H f.1 → InertK H p → ClauseInert Xo c la f k) ∧
    (InPsi H f.1 → Odd p → SplitK H p → ClauseSplit Xo c la f k) ∧
    (InPsi H f.1 → Odd p → InertK H p → 1 ≤ k → ClauseFine Xo c la f k)

def FactorBounds : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) → ∀ (p : ℕ) [Fact p.Prime], FactorBoundsAt Xo c p

def FactorDepthBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], FactorBounds Xo c

example : boundFine 3 1 0 1 1 = 1 ∧ upperInert 3 1 0 1 = 3 / 8 := by
  constructor
  · simp [boundFine]
  · norm_num [upperInert]

end GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds
