import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.BW

structure Rep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (μ : Measure (normOneGL E n))
    (v : LL μ) (φ : Sm E n) : Prop where
  umg : Umg φ
  cen : ∀ t g, φ.1 (zt E n t * g) = φ.1 g
  ae : (v : RightCosetSpace (rationalGLOne E n) → ℂ) =ᵐ[quotientMeasure (rationalGLOne E n) μ]
    fun y => φ.1 ((Quotient.out y : normOneGL E n) : GA E n)

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

def RepOps : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure], 0 < n → ∀ (v : LL μ) (φ : Sm E n), Rep μ v φ →
  (∀ ψ, Rep μ v ψ → φ = ψ) ∧ (∀ (v' : LL μ) ψ (c : ℂ), Rep μ v' ψ → Rep μ (c • v + v') (c • φ + ψ)) ∧
  (Cusp φ.1 → v ∈ cuspidalL2 μ) ∧
  ∀ (w : Pl E) (i : Fin n), (∀ k ∈ GlobalTheory.LFun.KGL w n, rw n w k φ = φ) → Rep μ (Tsph μ w i v) (hk n w (i + 1) φ)

def AmpRep : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (𝔞 : Amp μ), 0 < n →
  ∃ (ρ : Typ E n) (N : ℕ) (L : LL μ →ₗ[ℂ] Sm E n),
    (∀ v, Rep μ (𝔞.A v) (L v) ∧ Killed ρ.ρ (L v).1 ∧ Sph 𝔞.S (L v)) ∧
    (∀ u : UpperTheory.V.Cm.UC E n, ∃ B : ℝ, ∀ v g, ‖(UpperTheory.V.Cm.uC E n u (L v)).1 g‖ ≤ B * ‖v‖ * AutomorphicForm.height g ^ N) ∧
    ∀ x v, Rep μ (𝔞.Z x v) (zop (MvPolynomial.X x) (L v))

def DatDatum : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n), 2 ≤ d.len → ∃ b : Datum E n, (∃ Λ t, b.Pt S Λ t) ∧
  ∀ F : KF (Ix E n) (UpperTheory.ConvolutionTheory.Pl E × Fin n), (∀ x ∈ F.vars, x.1 ∉ S) → Kills S F b → d.Kills F

def BandRep : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (𝔞 : Amp μ) (η : ℝ), 0 < n → 0 < η →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : ℝ → ℝ, Continuous χ → (∀ x ≤ η / 2, χ x = 0) → ∀ (u : LL μ) (φ : Sm E n),
    Rep μ (fcalc χ 𝔞.A u) φ → Band C φ

end UpperTheory.ConvolutionTheory.BW
