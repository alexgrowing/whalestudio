import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions

open GlobalTheory.StdUnn

variable {D : D7}

def IsRowBasis {n : ℕ} (U : Submodule D.host.E (Fin n → D.host.E))
    (c : Matrix (Fin (Module.finrank D.host.E U)) (Fin n) D.host.E) : Prop :=
  LinearIndependent D.host.E c ∧ Submodule.span D.host.E (Set.range c) = U

def HermE (D : D7) (r : ℕ) : Type :=
  {b : Matrix (Fin r) (Fin r) D.host.E // (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}

def pull {m r n : ℕ} (c : Matrix (Fin r) (Fin n) D.host.E) (φ : Mx D m n → ℂ) : Mx D m r → ℂ :=
  fun y => φ (HMul.hMul y (c.map (incA D)))

def J (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b : HermE D r) : ℂ :=
  ∫ y, φ y * ψ (halfTr (Matrix.trace (HMul.hMul (b.1.map (incA D)) (inner V y y) : Mx D r r))) ∂μ

def Ifr (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ) : ℂ :=
  ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r},
    φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q ∂autMeasure V ν

def HidaSetting (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) : Prop :=
  1 ≤ n ∧ 2 * n < V.rank ∧ IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ V.rank ∧ IsInfFam θ ∧
    (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) ∧ IsWeilSch ψ χ θ V μ ω

def PullSch : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r n : ℕ) (c : Matrix (Fin r) (Fin n) D.host.E) (φ : Mx D m n → ℂ),
    φ ∈ schwartzA θ m n → pull c φ ∈ schwartzA θ m r

def EisCells : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 →
  ∀ (μr : ∀ r, Measure (Mx D V.rank r)), (∀ r, ∃ 𝓕, IsCovolOne (ratMx D V.rank r) (μr r) 𝓕) →
  ∀ c : ∀ U : Submodule D.host.E (Fin n → D.host.E), Matrix (Fin (Module.finrank D.host.E U)) (Fin n) D.host.E,
    (∀ U, IsRowBasis U (c U)) →
    HasSum (fun q : (Σ U : Submodule D.host.E (Fin n → D.host.E), HermE D (Module.finrank D.host.E U)) =>
        J ψ V (μr _) (pull (c q.1) Φ.1) q.2)
      (GlobalTheory.Eis.cosetSum (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1)

def ThetaOrbits : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤ →
  ∀ c : ∀ U : Submodule D.host.E (Fin n → D.host.E), Matrix (Fin (Module.finrank D.host.E U)) (Fin n) D.host.E,
    (∀ U, IsRowBasis U (c U)) →
    HasSum (fun U : Submodule D.host.E (Fin n → D.host.E) => Ifr V ν (pull (c U) Φ.1))
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν)

def BigCell : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank r)) (𝓕 : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μ 𝓕 →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    Summable (fun b : HermE D r => J ψ V μ φ b) →
    HasSum (fun b : HermE D r => J ψ V μ φ b) (Ifr V ν φ)

end PositivityTheory.GramSchwartzFunctions
