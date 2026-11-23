import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
import Development.AutomorphicArithmetic.WhittakerHecke.HasDerivAtWhittakerPeriodOneParameter
import Development.AutomorphicArithmetic.WhittakerHecke.ArchimedeanConjugateCurveOneParameterSubgroup
import Development.AutomorphicArithmetic.WhittakerHecke.DiagonalMulArchimedeanCurveEqUnipotentMul
import Development.AutomorphicArithmetic.WhittakerHecke.StandardAddCharNegArchimedeanRat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), Pp.Lf f.1 →
        (∀ X, Continuous (lie E 2 X f).1 ∧ ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) → ∀ (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)),
        Wo D (lie E 2 (toL (XB D k)) f).1 (em E (aE y) * k) = (2 * Real.pi * Complex.I * (re (y : A ℚ) : ℂ)) * Wo D f.1 (em E (aE y) * k) := by
  intro E _ _ _ D f hf hl y k
  obtain ⟨c0, cadd, cd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have h1 := UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) (toL (XB D k)) (em E (aE y) * k) c0 cadd cd hf.1 (hl _).1 (hl _).2
  have e : (fun t : ℝ => Wo D f.1 (em E (aE y) * k * infGL E 2 (cv D k t))) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * (re (y : A ℚ) : ℂ))) * Wo D f.1 (em E (aE y) * k) := by
    funext t
    rw [UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hf]
    have e1 : (![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] : Fin 2 → A ℚ) 1 = TR.sInf ℚ fun _ => t * re (y : A ℚ) := rfl
    rw [e1, UpperTheory.standardAddChar_neg_archimedean_rat]
    push_cast
    rfl
  rw [e] at h1
  have a : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 := (((a.mul_const (re (y : A ℚ) : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const
    (Wo D f.1 (em E (aE y) * k))
  have h3 := h1.unique h2
  rw [h3]
  simp
