import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.D.hatN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ b φ v, hat (W.Om (nU b) φ).1 v = ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * hat φ.1 (Function.update v 1 (v 1 + b * v 0)) := by
  intro F E _ _ _ _ _ _ _ D W b φ v
  have hψ : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := by
    intro x y
    simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hq : ∀ s : A F, q4 D.δ (Function.update v 1 s) = v 2 ^ 2 - rt D.δ * v 3 ^ 2 - s * v 0 := by
    intro s
    simp [q4]
  unfold hat
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have h : ψ (b * q4 D.δ (Function.update v 1 s)) * ψ (-(s * v 1)) =
      ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * ψ (-(s * (v 1 + b * v 0))) := by
    rw [← hψ, ← hψ, hq]
    congr 1
    ring
  simp only [W.Om_n, Function.update_idem, Function.update_self]
  linear_combination (φ.1 (Function.update v 1 s)) * h
