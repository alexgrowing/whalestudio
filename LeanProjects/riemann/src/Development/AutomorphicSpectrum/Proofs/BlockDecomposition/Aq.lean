import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Bq (ψ : AddChar F Circle) (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (g h : GL (Fin 2) F) : ℂ :=
  W₀ h * W' (h * g) * pFT ψ Φ g.val (e2r h) * mp (GeneralLinearGroup.det h) s

def Aq (ψ : AddChar F Circle) (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F) : ℂ :=
  mp (GeneralLinearGroup.det q.2) (s + 1 / 2) *
    (((GlobalTheory.CompanionTheory.DampedZetaMajorant.wR q.1 : ℝ) : ℂ) * Bq ψ W₀ W' Φ s q.2 (hI q.1 * q.2⁻¹))

open Classical in

def Mj (R B σ ε : ℝ) (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℝ :=
  if (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧ (modulus (p.2.1 : F) : ℝ) ≤ R ∧ (modulus (p.1 : F) : ℝ) ≤ B then
    (modulus (p.1 : F) : ℝ) ^ (σ + 1 - 2 * ε) * (modulus (p.2.1 : F) : ℝ) ^ (2 * σ) *
      ((modulus (g.val).det : ℝ) / GlobalTheory.CompanionTheory.GJTwo.mx (e2r (p.2.2 * g)) ^ 2) ^ (1 / 2 - ε)
  else 0

end D

end GlobalTheory.CompanionTheory.GL2Unfolding
