import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def vDiff_vp (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℝ :=
  (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) : ℝ) /
    (multiplicity w.asIdeal (Ideal.span {(p : 𝓞 E)}) : ℝ)

def SplitAt (H : Host E) (p : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal

def SplitQuad (H : Host E) (p : ℕ) : Prop :=
  (p = 2 ∧ H.d % 8 = 7) ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)

def RamifiedPrimes (H : Host E) (S : Finset ℕ) (q₁ : ℕ) : Prop :=
  IsAbelianGalois ℚ E ∧ q₁.Prime ∧ 11 ≤ q₁ ∧ q₁ % 8 = 3 ∧ q₁ ≠ H.d ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S ∨ p = q₁ ∨ p = H.d) ∧
    (2 ∈ S ∧ ∀ p ∈ S, p.Prime ∧ SplitQuad H p ∧ SplitAt H p) ∧ SplitAt H q₁ ∧ SplitAt H H.d

variable {H : Host E} {Dw : Datum H}

def IsBig (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ k ≤ rk f + 1

def IsSpread (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ rk f + 2 ≤ k

def IsSmall (f : Lt1 Dw) : Prop := ¬ InPsi H f.1

theorem not_isBig_iff (k : ℕ) (f : Lt1 Dw) : ¬ IsBig k f ↔ IsSmall f ∨ IsSpread k f := by
  unfold IsBig IsSmall IsSpread
  by_cases h : InPsi H f.1
  · simp only [h, true_and, not_true, false_or]; omega
  · simp [h]

open Classical in

def sumBig (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ := ∑ f ∈ Finset.univ.filter (IsBig k), cx f

open Classical in

def sumSmallSpread (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f => IsSmall f ∨ IsSpread k f), rk f * cx f

def boundTwo_vp (k : ℕ) (vd : ℝ) (cx : Lt1 Dw → ℕ) : ℝ :=
  (Dw.q : ℝ) * (1 + vd) * (sumBig k cx : ℝ) + (sumSmallSpread k cx : ℝ)

def boundSmall_vp (p k : ℕ) (vd : ℝ) (cx : Lt1 Dw → ℕ) : ℝ :=
  (Dw.q : ℝ) * (1 / ((p : ℝ) - 1) + vd) * (sumBig k cx : ℝ) + 1 / ((p : ℝ) - 1) * (sumSmallSpread k cx : ℝ)

def boundDeg_vp (p : ℕ) (cx : Lt1 Dw → ℕ) : ℝ := (degP cx : ℝ) / ((p : ℝ) - 1)

section Place

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime]

def DepthBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (B : ℝ) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    0 ≤ nuP p y cx ∧ nuP p y cx ≤ (B : EReal)

def OscBelow (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (B : ℝ) : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F), PointsOfFlagModel.BaseAt la.1 β → ∀ (Y : Model Xo c β) (Z : Comp Xo c),
    GenEx Y Z la.1 →
      eLoc Y Z la cx ≤ nuPSup (fun _ _ y => OnComp Z y ∧ y.IsAlg) la cx ∧
      nuPSup (fun _ _ y => OnComp Z y ∧ y.IsAlg) la cx ≤ (B : EReal) ∧
      eLoc Y Z la cx ≤ (B : EReal)

end Place

def UnscaledDepthBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Finset ℕ) (q₁ : ℕ), RamifiedPrimes H S q₁ →
    ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (Dw : Datum H) (k j : ℕ), 3 ≤ k → 1 ≤ j → Dw.p + 1 = k + j →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (cx : Lt1 Dw → ℕ),
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (la : PointsOfFlagModel.abelian₂ p c) (w : HeightOneSpectrum (𝓞 E)),
        (p : 𝓞 E) ∈ w.asIdeal →
        DepthBetween Xo c la cx (boundSmall_vp p k (vDiff_vp p w) cx) ∧
        OscBelow Xo c la cx (boundSmall_vp p k (vDiff_vp p w) cx)) ∧
      ∀ (p : ℕ) [Fact p.Prime], p = q₁ ∨ p = H.d → ∀ la : PointsOfFlagModel.abelian₂ p c,
        DepthBetween Xo c la cx (boundDeg_vp p cx) ∧ OscBelow Xo c la cx (boundDeg_vp p cx)

end GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification
