import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.GaussAct
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem finPart_mulVec {F : Type} [Field F] [NumberField F] (M : Matrix (Fin 4) (Fin 4) (A F))
    {v v' : V4 F} (e : finPartPi v = finPartPi v') : finPartPi (M *ᵥ v) = finPartPi (M *ᵥ v') := by
  funext i
  have e' : ∀ j, (v j).2 = (v' j).2 := fun j => congrFun e j
  let s : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have e'' : ∀ j, s (v j) = s (v' j) := e'
  change s ((M *ᵥ v) i) = s ((M *ᵥ v') i)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, e'']

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (h : GL (Fin 2) (A E)), (Matrix.GeneralLinearGroup.map (pInf E) h).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E) →
    ∀ φ ∈ Vac D.δ, W.L h φ ∈ Vac D.δ := by
  intro F E _ _ _ _ _ _ _ D W h hu φ hφ v v' e
  have hinv : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E) := by
    have hs := Unitary.star_mem hu
    have hm : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val = star (Matrix.GeneralLinearGroup.map (pInf E) h).val := by
      have h1 : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val * (Matrix.GeneralLinearGroup.map (pInf E) h).val = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have h2 : (Matrix.GeneralLinearGroup.map (pInf E) h).val * star (Matrix.GeneralLinearGroup.map (pInf E) h).val = 1 :=
        Unitary.mul_star_self_of_mem hu
      exact left_inv_eq_right_inv h1 h2
    rw [hm]
    exact hs
  have hg := gaussAct F E D h⁻¹ hinv
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hfin : finPartPi (D.act h⁻¹ v) = finPartPi (D.act h⁻¹ v') := by
    rw [hρ, hρ]
    exact finPart_mulVec _ e
  have key := hφ _ _ hfin
  rw [hg, hg] at key
  rw [W.L_apply, W.L_apply, mul_assoc, mul_assoc, key]
