import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.EqOfBelowSelf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.splt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      ∃ θ : Kv v, Splt D v θ ((lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)) := by
  intro F E _ _ _ _ _ D v w i hc hal
  obtain ⟨θ, hsq, hne, hk⟩ := UpperTheory.ConvolutionTheory.R2.I.place F E D v w i hc hal
  obtain ⟨-, -, -, -, hlc, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws E w
  have hone : ∀ a b : Fin 2, i ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) a b) =
      (1 : Matrix (Fin 2) (Fin 2) (Kv w)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨θ, hsq, hne, ?_, ?_⟩
  · intro x a b
    have e : (Matrix.GeneralLinearGroup.map i.toRingHom x).val a b = i (x.val a b) := rfl
    change (lc w (Matrix.GeneralLinearGroup.map i.toRingHom x)).val a b = _
    rw [hlc, e, ← hone, ← map_sub, hk]
  · intro x
    exact ⟨locGL E 2 w (Matrix.GeneralLinearGroup.map i.toRingHom x), rfl⟩
