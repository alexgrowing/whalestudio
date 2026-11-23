import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.DampedZetaMajorant

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def wR (p : Fˣ × Fˣ × GL (Fin 2) F) : ℝ := (modulus (p.1 : F) : ℝ)⁻¹

def Jm (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (ν' : Fˣ →* ℂˣ) (s : ℂ)
    (p : GL (Fin 2) F × Fˣ) : ℂ :=
  φ₀ (e1r p.1) * φ (e2r p.1) * (((ν' (GeneralLinearGroup.det p.1))⁻¹ : ℂˣ) : ℂ) *
    mp (GeneralLinearGroup.det p.1) (s + 1 / 2) *
    (V (dg2 p.2 1 * p.1) * ((ν' p.2 : ℂˣ) : ℂ) * mp p.2 (s - 1 / 2))

def Th (q : Fˣ × GL (Fin 2) F) : GL (Fin 2) F × Fˣ := (dg2 q.1 1 * q.2, q.1⁻¹)

end D

end GlobalTheory.CompanionTheory.DampedZetaMajorant
