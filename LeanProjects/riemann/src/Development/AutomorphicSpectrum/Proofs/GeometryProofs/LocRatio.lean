import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
