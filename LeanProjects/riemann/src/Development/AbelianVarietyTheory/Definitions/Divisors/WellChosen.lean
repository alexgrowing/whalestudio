import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

structure Quoted : Prop where
  kv : GlobalTheory.Published.KawamataViehweg
  l2 : GlobalTheory.Published.L2ExtensionLogCanonical
  gaga : GlobalTheory.Published.SerreHolomorphicSections
  nef : GlobalTheory.Published.NefNumerics
  chow : GlobalTheory.Published.ChowFormExists
  chowInt : GlobalTheory.Published.ChowFormIntExists
  chowCut : GlobalTheory.Published.ChowFormHyperplaneSection
  len : GlobalTheory.Published.ProperIntersectionLength

variable {F : Type} [Field F] [NumberField F]

def rho0 (T : Tuple F) (l : ℕ) : ℝ := 8 * T.D * T.del * T.n * l * T.abelian₂

def rho1 (T : Tuple F) (l : ℕ) : ℝ := rho0 T l * (1 + 1 / (8 * T.D * T.del))

structure WellChosen (T : Tuple F) (h : ℝ) (l : ℕ) (E : Type) [Field E] [NumberField E] [Algebra F E]
    (s : Fin T.D → Fin T.N → E) : Prop where
  lt_l : T.theta h ^ 20 < l
  l_le : (l : ℝ) ≤ 2 * T.theta h ^ 20
  mem : ∀ i, s i ∈ T.latticeOver E
  good : T.IsGoodSection E s
  card : ((T.geomPts E (T.linSection E s)).ncard : ℤ) = T.del
  ne : ∀ i, s i ≠ 0
  norm_le : ∀ i (τ : E →+* ℂ), T.normAt τ (s i) ≤ rho1 T l
  lower : ((T.D : ℝ) + 1) * T.del * h + T.D * T.del * Real.log (rho0 T l) -
    T.del * (((T.D : ℝ) + 1) * (harmonic (T.N - 1) : ℝ) / 2 + Real.log 2 / T.del + 1 / 8) ≤
      T.cycleHeight E (T.linSection E s)
  upper : T.cycleHeight E (T.linSection E s) ≤ ((T.D : ℝ) + 1) * T.del * h + T.del * ∑ i, T.meanLogNorm (s i)
  residue : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P

def DelPos : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational → 0 < T.del

def Choice : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), IsTotallyComplex F → T.IsAdelic → ∀ h, T.IsHeight h →
    ∃ (l : ℕ) (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (s : Fin T.D → Fin T.N → E),
      WellChosen T h l E s

def Split (T : Tuple F) (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop :=
  ∀ x : Sp (AlgebraicClosure E) ⟶ (T.linSection E s).subscheme,
    x ≫ (T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str = spMap (algebraMap E (AlgebraicClosure E)) →
    ∃ x₀ : Sp E ⟶ (T.linSection E s).subscheme, x = spMap (algebraMap E (AlgebraicClosure E)) ≫ x₀

structure Coord {K : Type} [Field K] [NumberField K] (G : Geo K) {s : Fin G.D → Fin G.N → K} (hs : G.IsGood s) (δ : ℕ) where

  ev : ∀ j : ℕ, G.SecOn s j ≃ₗ[K] (Fin δ → K)

  y : Fin δ → Fin G.N → K

  c₂ : (K →+* ℂ) → Fin δ → ℝ
  y_ne : ∀ p, y p ≠ 0
  c₂_pos : ∀ σ p, 0 < c₂ σ p
  c₂_conj : ∀ σ p, c₂ ((starRingEnd ℂ).comp σ) p = c₂ σ p
  mul : ∀ (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j),
    ev (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) = fun p => (∑ k, u k * y p k) * ev j g p
  sq : ∀ (j : ℕ) (σ : K →+* ℂ) (m : ℕ) (c : Fin m → ℂ) (g : Fin m → G.SecOn s j),
    csq (hs.normOn j) σ c g =
      ∑ p, ‖∑ i, c i * σ (ev j (g i) p)‖ ^ 2 / (c₂ σ p * archSize (G.A σ) (fun k => σ (y p k)) ^ j) ^ 2

def Claim (X : Data F) (C h J : ℝ) : Prop :=
  0 ≤ X.z ∧ X.z ≤ 1 ∧
    (1 - X.z) * (X.T * h - 3 * ((X.D : ℝ) + 1) * |h| - J - C * (X.D : ℝ) ^ 2 * (X.logRho C h + Real.log X.T) -
        ((X.T : ℝ) + X.D + 1) * Real.log X.beta - ((X.T : ℝ) + (X.D : ℝ) ^ 2) * (X.g + 2)) -
      X.z * (X.T * (Real.log 2 + X.logRho C h + Real.log X.beta / 2) + Real.log X.LamD + Real.log X.LamT) ≤
    X.degM X.T / X.d

def HSBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F), X.Hyp → ∀ h, X.IsHeight h → ∀ C, 26 ≤ C → 0 < X.d ∧ Claim X C h X.J

def RankLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : Geo F), IsNef F G.LA → IsBig F G.LA → ∀ T : ℕ,
    ((T - 1).choose G.D : ℤ) * G.del ≤ Module.finrank F (G.global T)

def KerRes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ l : ℕ, G.D ≤ l + 1 →
      ∀ f ∈ Fil (G.ideal s) 1 (G.global (l + 1)), ∃ m : Fin G.D → G.Sec l, (∀ i, m i ∈ G.global l) ∧ f = ∑ i, G.mulW l (s i) (m i)

def FilMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ (a j l : ℕ) (h : j + a = l), G.D ≤ j →
      ∀ f ∈ Fil (G.ideal s) a (G.global l), ∃ m : MonoDeg (Fin G.D) a → G.Sec j,
        (∀ α, m α ∈ G.global j) ∧ f = ∑ α, mulPow G s h α (m α)

def Extension : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s), (∀ i, s i ≠ 0) →
    ∀ (σ : K →+* ℂ) (j : ℕ), G.D ≤ j → ExtensionBound σ hs j

example (X : Data F) (C h J : ℝ) (H : Claim X C h J) : X.z ≤ 1 := H.2.1

end GlobalTheory.HSCore
