import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem diagonal_mul_gl_conj {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (g : G1 F) :
    dM t * gl g = gl (cD t g) * dM t := by
  apply Units.ext
  ext i j
  have h1 : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv t
  fin_cases i <;> fin_cases j <;>
    simp [dM, cD, gl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGL, mul_assoc, h1, mul_comm]

private theorem Wf_tr {F : Type} [Field F] [NumberField F] (f : GL (Fin 2) (A F) → ℂ) (x g₀ : G1 F) (t : (A F)ˣ) :
    Wf (fun g => f (g * gl g₀)) (gl x * dM t) = Wf f (gl (x * cD t g₀) * dM t) := by
  have e : ∀ b, gl (nU b) * (gl x * dM t) * gl g₀ = gl (nU b) * (gl (x * cD t g₀) * dM t) := by
    intro b
    have hg : gl (x * cD t g₀) = gl x * gl (cD t g₀) := map_mul Matrix.SpecialLinearGroup.toGL _ _
    rw [mul_assoc, mul_assoc, diagonal_mul_gl_conj, hg, mul_assoc]
  simp only [Wf, e]

private theorem Om_tr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (φ : S4 F) (h : GL (Fin 2) (A E)) (x g₀ : G1 F) :
    W.Om x (W.L h (W.Om g₀ φ)) = W.Om (x * cD (nu F h) g₀) (W.L h φ) := by
  have hL := LinearMap.congr_fun (W.comm h g₀) φ
  simp only [Module.End.mul_apply] at hL
  rw [hL, map_mul, Module.End.mul_apply]

private theorem weilLift_translate {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (g₀ x : G1 F) :
    w1 W (fun g => f (g * gl g₀)) (W.Om g₀ φ) h x = w1 W f φ h (x * cD (nu F h) g₀) := by
  simp only [w1]
  rw [Wf_tr, Om_tr]

theorem UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h (g₀ : G1 F),
      W1 W M (fun g => f.1 (g * gl g₀)) (W.Om g₀ φ) h = W1 W M f.1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h g₀
  obtain ⟨-, -, hm, hN, hi⟩ := conv F E D W M π f hf φ hφ h
  have key : w1 W (fun g => f.1 (g * gl g₀)) (W.Om g₀ φ) h =
      fun x => w1 W f.1 φ h (x * cD (nu F h) g₀) := funext (weilLift_translate W f.1 φ h g₀)
  unfold W1
  rw [key]
  exact ((inv F M (w1 W f.1 φ h) hm hN hi).1 (cD (nu F h) g₀)).2
