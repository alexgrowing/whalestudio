import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

variable {F : Type} [Field F] [NumberField F]

private theorem one_int (h : (Fin 1 → A F) → ℂ) :
    ∫ a, h a ∂(adeleMeasurePi F) = ∫ s : A F, h (fun _ => s) ∂(adeleMeasure F) :=
  ((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm

private theorem reindex_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    {f : (κ → A F) → ℂ} (hf : f ∈ schwartzBruhatPi F κ) :
    (fun x : ι → A F => f (x ∘ e)) ∈ schwartzBruhatPi F ι := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi
    ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e)
    (by rw [Matrix.submatrix_mul_equiv]; simp) (by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]) hf
  convert h using 2
  rename_i x
  congr 1
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private def eS : Fin 4 ≃ Fin 3 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1, .inl 2]
  invFun := Sum.elim ![0, 2, 3] fun _ => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    rintro (i | i)
    · fin_cases i <;> rfl
    · fin_cases i; rfl

private theorem slice_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) (v : V4 F) :
    (fun y : Fin 1 → A F => φ (Function.update v 1 (y 0))) ∈ schwartzBruhatPi F (Fin 1) := by
  have h1 := reindex_mem (F := F) eS hφ
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![v 0, v 2, v 3]
  convert h2 using 2
  rename_i y
  congr 1
  ext i
  fin_cases i <;> simp [eS, Function.update]

end UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

open UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance in
theorem UpperTheory.ConvolutionTheory.R2.G.hatInv :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F) (v : V4 F), hat (hat φ.1) v = φ.1 (Function.update v 1 (-v 1)) := by
  intro F _ _ φ v
  have hg := slice_mem φ.2 v
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have key : ∀ s : A F, hat φ.1 (Function.update v 1 (-s)) =
      adelicFourierPi F (fun y : Fin 1 → A F => φ.1 (Function.update v 1 (y 0))) (fun _ => s) := by
    intro s
    rw [hat, adelicFourierPi, one_int]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [ψ]
  rw [hat, ← integral_neg_eq_self]
  refine Eq.trans ?_ (inv.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [key]
    simp [ψ]
  · simp
