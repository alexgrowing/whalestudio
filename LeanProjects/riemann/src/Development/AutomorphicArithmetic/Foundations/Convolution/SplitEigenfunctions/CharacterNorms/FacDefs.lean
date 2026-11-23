import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

def pv (v : H.P ℚ) : (A ℚ)ˣ := H.idl v (atFin v (unif v))

def pin (n : ℕ) : (A ℚ)ˣ := ∏ᶠ v : H.P ℚ, pv v ^ (n.factorization (normV v))

def TT (L : ℕ) : Set (A ℚ)ˣ := {t | t ∈ UU ∧ ∀ v, Dv L v ((t : A ℚ) - 1)}

def cT (L : ℕ) : ℝ := (finiteIdeleMeasure ℚ ((fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L)).toReal

def SS (N : ℕ) : Set (G1 ℚ) := {k | ∀ v, Dv N v (k 1 0)}

def cK (M : Meas ℚ) (N : ℕ) : ℝ := (M.κ (SS N ∩ KK ℚ)).toReal

def sqN (N : ℕ) (n : ℕ) : ℂ := if ∃ m : ℕ, n = m * m ∧ m.Coprime N then 1 else 0

def bN (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Coprime N then (n : ℂ) * ((χ.1 (pin n) : ℂˣ) : ℂ) * μ n else 0

variable {E : Type} [Field E] [NumberField E]

def Yt (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (g : GL (Fin 2) (A ℚ)) : ℂ :=
  ∫ y : IdeleGroup ℚ, Wo D φ (em E (aE y * g)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) ∂(ideleMeasure ℚ)

def It (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ 0 * ((|y| : ℝ) : ℂ) ^ (s - 2)

def Zr (N : ℕ) (p : MvPolynomial (Fin 2) ℂ) (s : ℂ) (k : G1 ℚ) : ℂ :=
  ∫ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s) ∂(ideleMeasure ℚ)

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
