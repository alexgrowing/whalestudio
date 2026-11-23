import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfT
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem conj_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    {ξ : Fin 2 → F} (hξ : ξ ≠ 0) : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0 := by
  intro h
  have hl := Fintype.linearIndependent_iff.1 D.b.linearIndependent ![ξ 0, -ξ 1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, D.b0, D.b1, Algebra.smul_def, map_neg]
    simp only [Matrix.cons_val_fin_one, mul_one, map_neg]
    linear_combination h)
  apply hξ
  ext i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1

private theorem coe_al {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (ξ : Fin 2 → F) (h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0) :
    ((al D ξ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (-rt (ξ 1)) := by
  have e := D.mkE_rt (ξ 0) (-ξ 1)
  have e' : -rt (ξ 1) = (rt (-ξ 1) : A F) := (map_neg _ _).symm
  rw [e', e, al, dif_neg h, IdeleGroup.coe_diagonal]
  simp [sub_eq_add_neg]

private theorem vcD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    (gl (cD t x)).val = !![x 0 0, x 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * x 1 0, x 1 1] := rfl

private theorem vgl {F : Type} [Field F] [NumberField F] (x : G1 F) : (gl x).val = x.1 := rfl

private theorem vmD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    (gl (mD t)).val = !![(t : A F), 0; 0, ((t⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem cD_dM {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    gl (cD t x) * dM t = dM t * gl x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vcD, vgl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> ring

private theorem dM_mD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : dM t * gl (mD t) = aE t := by
  refine Units.ext ?_
  rw [Units.val_mul, vmD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pt_move {F : Type} [Field F] [NumberField F] (t n : (A F)ˣ) (g : G1 F) :
    gl (cD t (mD t * g)) * dM (t * n) = aE t * (gl g * dM n) := by
  rw [UpperTheory.ConvolutionTheory.R2.dM_mul, ← mul_assoc, cD_dM, gl_mul, ← mul_assoc (dM t), dM_mD, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.wxPt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (ξ : Fin 2 → F), ξ ≠ 0 → ∃ t : Fˣ, ∀ f : GL (Fin 2) (A F) → ℂ, Pp.Lf f → ∀ φ h g,
    w1 W f φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) (mD (IdeleGroup.diagonal F t) * g)) = wx W f φ h ξ g := by
  intro F E _ _ _ _ _ _ _ D W ξ hξ
  have hz := conj_ne D hξ
  have hα := coe_al D ξ hz
  set α := al D ξ with hαdef
  let t : Fˣ := Units.map (Algebra.norm F : E →* F) (Units.mk0 _ hz)
  have hT : ideleNorm F E α = IdeleGroup.diagonal F t := by
    rw [hαdef, al, dif_neg hz, ideleNorm_diagonal]
  have hco : D.co (α : A E) = ![rt (ξ 0), -rt (ξ 1)] := by rw [hα, D.co_mkE]
  have ht : (t : F) = ξ 0 ^ 2 - D.δ * ξ 1 ^ 2 := by
    haveI := AdeleBaseChange.nontrivial_adeleRing F
    apply (algebraMap F (A F)).injective
    have h1 := D.coe_ideleNorm α
    rw [hT, IdeleGroup.coe_diagonal, hco] at h1
    simpa using h1
  refine ⟨t, fun f hf φ h g => ?_⟩
  set T := IdeleGroup.diagonal F t with hTdef
  have hnu : nu F (aE α * h) = T * nu F h := by rw [nu_mul, nu_aE, hT]
  have hpoint : ![T * (0 : A F), ((T⁻¹ : (A F)ˣ) : A F) * ((ideleNorm F E α : (A F)ˣ) * 1),
      T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 0, T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 1] = pt ξ := by
    have hb : am E (T : A F) * ((α⁻¹ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (rt (ξ 1)) := by
      rw [← hT, D.am_ideleNorm, mul_comm (α : A E), mul_assoc, Units.mul_inv, mul_one, hα, D.bar_mkE, neg_neg]
    have hc := D.co_am_mul (T : A F) ((α⁻¹ : (A E)ˣ) : A E)
    rw [hb, D.co_mkE] at hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [D.mkE_one, mul_one, hT]
    simp [pt, ← h0, ← h1]
  have hhat : hat (W.Om (cD T (mD T * g)) (W.L (aE α * h) φ)).1 ![0, 1, 1, 0] = hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    have hcm : W.Om (cD T (mD T * g)) (W.L (aE α) (W.L h φ)) = W.L (aE α) (W.Om (mD T * g) (W.L h φ)) := by
      have := W.comm (aE α) (mD T * g)
      rw [nu_aE, hT] at this
      exact (LinearMap.congr_fun this (W.L h φ)).symm
    rw [map_mul, Module.End.mul_apply, hcm]
    have hS := hatSt F E D W
    have e1 := hS.aE α (W.Om (mD T * g) (W.L h φ)) 0 1 1 0
    have e2 := hS.m T (W.Om g (W.L h φ))
    have e3 : ((W.η.1 T : ℂˣ) : ℂ) = 1 := by rw [← hT, W.η_norm]; rfl
    have e4 : ab T = 1 := ab_diagonal t
    rw [e1, map_mul, Module.End.mul_apply, e2, e3, e4]
    have hv := hpoint
    rw [← hv]
    simp
  have hw : ∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F) =
      Wf f (aE T * (gl g * dM (nu F h))) := by
    rw [← ht]
    exact Pp.wfT F f hf t _
  simp only [w1, wx]
  rw [hhat, hnu, pt_move, hw]
