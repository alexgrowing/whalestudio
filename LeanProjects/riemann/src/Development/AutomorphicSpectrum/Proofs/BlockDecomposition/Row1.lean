import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mx (r : Fin 2 → F) : ℝ := max (modulus (r 0) : ℝ) (modulus (r 1) : ℝ)

def row1 (r₂ : Fin 2 → F) (x y : F) : Fin 2 → F := ![y / r₂ 1 + x * r₂ 0, x * r₂ 1]

def cM (ψ : AddChar F Circle) : Measure ((Fin 2 → F) × F × F) :=
  (LFS.vol2 ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))

open Classical in

def Ff (f : GL (Fin 2) F → ℂ) (p : (Fin 2 → F) × F × F) : ℂ :=
  if h : p.2.2 = 0 ∨ p.1 1 = 0 then 0 else
    f (uni2 p.2.1 * dg2 (Units.mk0 p.2.2 (fun e => h (Or.inl e))) 1 * hr p.1) *
      (((modulus p.2.2 : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)

def zI (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (g : GL (Fin 2) F) : F → ℂ :=
  onU fun a => W (dg2 a 1 * g) * ((μ a : ℂˣ) : ℂ) * mp a (s - 3 / 2)

end D

end GlobalTheory.CompanionTheory.GJTwo
