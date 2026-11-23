import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.conjStep :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (α : (A E)ˣ),
      Measurable (w1 W f φ (aE α)) → (∀ b g, w1 W f φ (aE α) (nU b * g) = w1 W f φ (aE α) g) → Integrable (iw (w1 W f φ (aE α))) M.ν →
      W1 W M f φ (aE α) = ((ab (ideleNorm F E α) : ℝ) : ℂ) * M.I0 fun g => Wf f (dM (ideleNorm F E α) * gl g) *
        hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
  intro F E _ _ _ _ _ _ _ D W M f φ α h1 h2 h3
  have hn : nu F (aE α) = ideleNorm F E α := by
    unfold nu
    congr 1
    exact Units.ext (by simp [aE, Matrix.det_fin_two])
  have h4 := ((UpperTheory.ConvolutionTheory.R2.inv F M _ h1 h2 h3).2 (ideleNorm F E α)).2
  have hab : ((ab (ideleNorm F E α) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F (ideleNorm F E α)).2.ne'
  have h5 : (fun g => w1 W f φ (aE α) (cD (ideleNorm F E α) g)) = fun g => Wf f (dM (ideleNorm F E α) * gl g) *
      hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
    funext g
    have e1 : gl (cD (ideleNorm F E α) g) * dM (ideleNorm F E α) = dM (ideleNorm F E α) * gl g := by
      generalize ideleNorm F E α = t
      refine Units.ext ?_
      show (cD t g).1 * (dM t).val = (dM t).val * g.1
      ext i j : 2
      fin_cases i <;> fin_cases j <;> simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    have e2 : W.Om (cD (ideleNorm F E α) g) (W.L (aE α) φ) = W.L (aE α) (W.Om g φ) := by
      have := LinearMap.congr_fun (W.comm (aE α) g) φ
      rw [hn] at this
      exact this.symm
    have e3 : D.mkE 1 0 = 1 := by simp [Dat.mkE]
    rw [w1, hn, e1, e2, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).aE, e3, mul_one, mul_one]
  rw [← h5, h4, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hab, one_mul]
  rfl
