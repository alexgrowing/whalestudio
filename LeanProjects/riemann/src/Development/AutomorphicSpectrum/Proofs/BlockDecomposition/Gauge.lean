import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2ZetaUnfolding

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def box2 (R : ℝ) : Set (Matrix (Fin 2) (Fin 2) F) := {A | ∀ i j, (modulus (A i j) : ℝ) ≤ R}

def vbox (R : ℝ) : Set (Fin 2 → F) := {v | ∀ i, (modulus (v i) : ℝ) ≤ R}

def Gauge (W : GL (Fin 2) F → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
      (W (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

open Classical in

def mjr (W₁ W₂ : GL (Fin 2) F → ℂ) (τ R : ℝ) (p : Fˣ × Fˣ × GL (Fin 2) F) (g : GL (Fin 2) F) : ENNReal :=
  if g.val ∈ box2 R ∧ e2r (hI p) ∈ vbox R then
    ENNReal.ofReal (‖W₁ (hI p)‖ * ‖W₂ (hI p * g)‖ * (modulus (p.1 : F) : ℝ) ^ (τ - 1) *
      (modulus (p.2.1 : F) : ℝ) ^ (2 * τ) * (modulus ((g.val).det) : ℝ) ^ (τ + 1 / 2))
  else 0

def large₂ (ψ : AddChar F Circle) (W₂ : GL (Fin 2) F → ℂ) (τ R : ℝ) (a : Fˣ) : ENNReal :=
  ∫⁻ g, (box2 R).indicator (fun _ => (1 : ENNReal)) g.val *
    ENNReal.ofReal (‖W₂ (dg2 a 1 * g)‖ * (modulus ((g.val).det) : ℝ) ^ (τ + 1 / 2)) ∂LFS.hG ψ

end D

end GlobalTheory.CompanionTheory.GL2ZetaUnfolding
