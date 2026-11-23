import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hermAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  ((gramAt D V τ)⁻¹ * wᴴ * gramAt D W τ * z).trace

def symplAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hermAt V W τ z w).re

open Classical in

def commScalar (V W : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  if τ = τ' then -(2 * Real.pi * Complex.I) * (symplAt V W τ z w : ℂ) else 0

def Cocompact (V W : HSp D) : Prop := CompactSpace (WO V W ⧸ (ratL W V : AddSubgroup (WO V W)))

def SquareIntegrable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ f, IsThetaFunO ψ V W f →
    (∀ γ ∈ ratL W V, ∀ x : WO V W, ‖f (γ + x)‖ = ‖f x‖) ∧
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      MemLp f 2 (μ.restrict 𝓕)

def HeisUnitary (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  (∀ (u v : WO V W) (f : WO V W → ℂ),
    heisO ψ V W u (heisO ψ V W v f) = ψ (symplOH V W u v) • heisO ψ V W (u + v) f) ∧
  (∀ (u : WO V W) (f : WO V W → ℂ), heisO ψ V W (-u) (heisO ψ V W u f) = f) ∧
  (∀ u f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (heisO ψ V W u f)) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
    ∀ u f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f') ∧
  ∀ γ ∈ ratL W V, ∀ f, IsThetaFunO ψ V W f → heisO ψ V W γ f 0 = f 0

def DerSkew (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ f, IsThetaFunO ψ V W f → ∀ x, HasDerivAt (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) f x)
      (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f x) 0) ∧
    (∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f)) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
        ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) f' =
          -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f')

def DerComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ s t : ℝ, ψ (symplO V W (lineAt θ τ z s) (lineAt θ τ' w t)) =
      Complex.exp (s * t * commScalar V W τ τ' z w)) ∧
    ∀ f, IsThetaFunO ψ V W f →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w f) -
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
          commScalar V W τ τ' z w • f

def FinRealComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ u : WO V W, u.map (infPart D) = 0 →
    (∀ v : WO V W, v.map (finPart D) = 0 → ∀ f : WO V W → ℂ,
      heisO ψ V W u (heisO ψ V W v f) = heisO ψ V W v (heisO ψ V W u f)) ∧
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      heisO ψ V W u (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (heisO ψ V W u f)

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ V W : HSp D, Cocompact V W ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      SquareIntegrable ψ V W ∧ HeisUnitary ψ V W ∧
        ∀ θ : InfFam D, IsInfFam θ → DerSkew ψ θ V W ∧ DerComm ψ θ V W ∧ FinRealComm ψ θ V W

example (D : D7) (m n : ℕ) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n))) (𝓕 : Set (WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n)))
    (f : WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n) → ℂ), IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL (GlobalTheory.Size.posSp D n) (GlobalTheory.Size.posSp D m)) 𝓕 μ ∧ IsThetaFunO ψ _ _ f ∧
      ipO μ 𝓕 f f ≠ 0 := by
  obtain ⟨ψ, θ, μ, 𝓕, U, f, h1, h2, h3, -, h5, h6, -⟩ := GlobalTheory.Size.exists_theta_posSp D m n
  exact ⟨ψ, θ, μ, 𝓕, f, h1, h2, h3.1, h3.2.1, h5.1, h6⟩

example (D : D7) (m n : ℕ) (τ : D.what₂.Tau) (z : Matrix (Fin (GlobalTheory.Size.posSp D n).rank) (Fin (GlobalTheory.Size.posSp D m).rank) ℂ)
    (hz : (zᴴ * z).trace.im = 0) :
    symplAt (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n) τ (Complex.I • z) z =
      -2 * (tauE D τ D.host.xi0).im * (zᴴ * z).trace.re := by
  simp only [symplAt, hermAt, GlobalTheory.Size.gramAt_posSp, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hz]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

end
