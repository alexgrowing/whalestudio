import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.SiegelFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

def IndepT (D : D7) (m r : ℕ) : Type :=
  {ξ : Matrix (Fin m) (Fin r) D.host.E // Function.Injective ξ.mulVec}

def HermQ (D : D7) (r : ℕ) : Type :=
  {b : Matrix (Fin r) (Fin r) D.host.E // ∀ i j, D.sp.cm.sig (b j i) = b i j}

variable {D : D7}

def indTheta (V : HSp D) {r : ℕ} (Φ : Mx D V.rank r → ℂ) (h : GA D V) : ℂ :=
  ∑' ξ : IndepT D V.rank r, Φ (invPt V h ξ.1)

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (Φ : Mx D V.rank r → ℂ)
    (b : HermQ D r) : ℂ :=
  ∫ y, Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (b.1.map (incA D)) (inner V y y) : Mx D r r))) ∂μ

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

def CoreFormula : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D), 1 ≤ r → 2 * r < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank r)) (𝓕 : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μ 𝓕 →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∀ Φ : schwartzA θ V.rank r,
    Summable (fun b : HermQ D r => ‖cellTerm ψ V μ Φ.1 b‖) ∧
      ⨍ q, AutomorphicL2Unitary.descend (GQ V) (indTheta V Φ.1) q ∂autMeasure V ν = ∑' b : HermQ D r, cellTerm ψ V μ Φ.1 b

def ValueFormula : Prop :=
  ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → 2 * A.rank < B.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f →
  ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) 1 →
    cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) 1 =
      ⨍ q, AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ω 1 h f) q ∂autMeasure B m

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

end
