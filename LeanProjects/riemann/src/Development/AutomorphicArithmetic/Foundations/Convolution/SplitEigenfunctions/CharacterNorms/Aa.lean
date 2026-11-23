import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.cov (t : ℝ) (u : IdeleGroup ℚ) (α : ℚˣ) : IdeleGroup ℚ :=
  IdeleGroup.diagonal ℚ α * (iy (Real.exp t) * iy (Real.exp t)) * u

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.Fb {E : Type} [Field E] [NumberField E] (φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ b in fundamentalSet ℚ, φ (em E (gl (nU b)) * h) ∂(adeleMeasure ℚ)

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.aa (t : ℝ) (u z : IdeleGroup ℚ) : IdeleGroup ℚ := iy (Real.exp t) * u * z⁻¹

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.Tt {E : Type} [Field E] [NumberField E] (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (u : IdeleGroup ℚ)
    (p : IdeleGroup ℚ × G1 ℚ) : ℂ :=
  (((ab (Un.aa t u p.1))⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ (em E (gl (mD (Un.aa t u p.1)) * dM u * gl p.2)) *
    Φ fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1)) * dM u * gl p.2).val 1 j

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.Hh {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ)
    (q : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ) : ℂ :=
  Wo D φ (em E (aE q.1 * gl q.2.2)) * ((χ.1 q.1 : ℂˣ) : ℂ) * ((ab q.1 : ℝ) : ℂ) ^ (s - 1) *
    ((Φ fun j => ((q.2.1 : (A ℚ)ˣ) : A ℚ) * row q.2.2 j) * ((ab q.2.1 : ℝ) : ℂ) ^ (2 * s))

def UpperTheory.ConvolutionTheory.RankTwoDescent.Un.Uu {E : Type} [Field E] [NumberField E] (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (u : IdeleGroup ℚ)
    (g : G1 ℚ) : ℂ :=
  φ (em E (gl g * dM u)) * Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j

end
