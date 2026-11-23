import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

namespace GlobalTheory.HSApp

def AmpleAt {Y : Scheme.{0}} (N : LB Y) (y : Y) : Prop :=
  ∃ (m : ℕ) (A : LB Y) (s : (LB.div (lbPow N m) A).Sec), 0 < m ∧ A.IsLB ∧ IsAmpleLB A ∧ y ∈ nonzeroLocus s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def GapGe (g : ℤ) (la : AllWt.Weight Dw) : Prop := ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → g ≤ gap (la τ) k

structure WtBig (P : WtPar Dw) : Prop where
  gaps : GapGe (((dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) : ℕ) : ℤ) P.u₁
  le_T : dimFlag Dw + 1 ≤ P.T
  one_le : 1 ≤ dimFlag Dw

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def CuspIso (la : AllWt.Weight Dw) : Prop := Extends X Z U la ∧ vanBd X Z la ≤ space X Z U la

def Steep (la : AllWt.Weight Dw) : Prop :=
  ∃ s : space X Z U la, s ≠ 0 ∧ ∀ (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) (Δ : Cartier ((baseId X Z U la).comap M.σ)),
    ∀ y ∈ M.bd, y ∉ nonzeroLocus (toSec (Δ.lift s))

variable {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)

def BergLe (la : AllWt.Weight Dw) (β : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, FD.Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw la 0) y ≤ ENNReal.ofReal β

theorem GapGe.mono {g g' : ℤ} {la : AllWt.Weight Dw} (h : GapGe g la) (e : g' ≤ g) : GapGe g' la :=
  fun τ k hk => e.trans (h τ k hk)

end GlobalTheory.HSApp
