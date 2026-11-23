import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mM (ψ : AddChar F Circle) : Measure (Fin 2 × Fin 2 → F) := Measure.pi fun _ => selfDualMeasure ψ

def toM (X : Fin 2 × Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => X (i, j)

def e1 : Fin 2 → F := ![1, 0]

def col2 (x : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := !![x 0, 0; x 1, 1]

def Pf (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F) (M : Matrix (Fin 2) (Fin 2) F) : ℂ :=
  Φ (cat3 ((z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1))

def Lpart (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ) : ℂ :=
  ∫ x, p (col2 x) * (ψ (-x 1) : ℂ) ∂LFS.vol2 ψ

def Rpart (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ) : ℂ :=
  ∫ X, p (toM X) * (ψ (-(X (0, 1) + X (1, 0))) : ℂ) ∂mM ψ

def rr (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ) (c : F) : ℂ :=
  ∫ a, ∫ b, ∫ d, p !![a, b; d, c] * (ψ (-(b + d)) : ℂ) ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ

end D

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair
