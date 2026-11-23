import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem nu_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h h' : GL (Fin 2) (A E)) : nu F (h * h') = nu F h * nu F h' := by
  simp only [nu, map_mul]

private theorem nu_gl' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (b : A E) : nu F (gl (nU b)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (gl (nU b)) = 1 := by
    exact Units.ext (nU b).2
  simp only [nu, h, map_one]

private theorem dM_mul' {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) :
    dM (s * t) = dM s * dM t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cD_one' {F : Type} [Field F] [NumberField F] (g : G1 F) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem Wf_tr {F : Type} [Field F] [NumberField F] (f : GL (Fin 2) (A F) → ℂ)
    (x y : GL (Fin 2) (A F)) : Wf (fun g => f (g * x)) y = Wf f (y * x) := by
  simp only [Wf, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)),
      (∀ h₀, W1 W M f φ (h * h₀) = W1 W M (fun g => f (g * dM (nu F h₀))) (W.L h₀ φ) h) ∧
      ∀ u t, W1 W M f φ (gl (nU (D.mkE u t)) * h) = ψ (-(2 * u)) * W1 W M f φ h := by
  intro F E _ _ _ _ _ _ _ D W M f φ h
  constructor
  · intro h₀
    have key : w1 W f φ (h * h₀) = w1 W (fun g => f (g * dM (nu F h₀))) (W.L h₀ φ) h := by
      funext g
      simp only [w1]
      rw [Wf_tr, nu_mul', dM_mul', map_mul, Module.End.mul_apply, mul_assoc]
    simp only [W1, key]
  · intro u t
    have hn := nu_gl' (F := F) (D.mkE u t)
    have key : ∀ g, w1 W f φ (gl (nU (D.mkE u t)) * h) g = ψ (-(2 * u)) * w1 W f φ h g := by
      intro g
      have hc : W.Om g (W.L (gl (nU (D.mkE u t))) (W.L h φ)) =
          W.L (gl (nU (D.mkE u t))) (W.Om g (W.L h φ)) := by
        have := congrArg (fun T : Module.End ℂ (S4 F) => T (W.L h φ)) (W.comm (gl (nU (D.mkE u t))) g)
        simp only [Module.End.mul_apply, hn, cD_one'] at this
        exact this.symm
      have hne := (hatSt F E D W).nE u t (W.Om g (W.L h φ)) 1 1 0
      have hs : -(1 * (2 * (u * 1 - rt D.δ * (t * 0)))) = -(2 * u) := by
        simp
      rw [hs] at hne
      simp only [w1]
      rw [nu_mul', hn, one_mul, map_mul, Module.End.mul_apply, hc, hne]
      ring
    simp only [W1, Meas.I0, iw, key]
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
