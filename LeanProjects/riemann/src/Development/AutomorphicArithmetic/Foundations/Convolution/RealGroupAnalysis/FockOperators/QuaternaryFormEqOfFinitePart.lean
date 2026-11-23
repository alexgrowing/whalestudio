import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ActFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem mul_eq_of_inf_zero {F : Type} [Field F] [NumberField F] (x u u' : A F) (hx : x.1 = 0)
    (h : u.2 = u'.2) : x * u = x * u' := by
  apply Prod.ext
  · change x.1 * u.1 = x.1 * u'.1
    rw [hx, zero_mul, zero_mul]
  · change x.2 * u.2 = x.2 * u'.2
    rw [h]

private theorem quaternaryForm_eq_of_finitePart {F : Type} [Field F] [NumberField F] (δ : F) (a v v' : V4 F)
    (ha : ∀ i, (a i).1 = 0) (h : finPartPi v = finPartPi v') : B4 δ a v = B4 δ a v' := by
  have e : ∀ i j, a i * v j = a i * v' j := fun i j =>
    mul_eq_of_inf_zero _ _ _ (ha i) (congrFun h j)
  simp only [B4, e]

theorem UpperTheory.ConvolutionTheory.R2.Fo.lFix :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (y : GL (Fin 2) (Cinf E)) Λ, ∀ φ ∈ Fix D.δ Λ, W.L (infGL E 2 y) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W y Λ φ hφ
  have hφ' : ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
      φ.1 (v + a) = φ.1 v ∧ ψ (B4 D.δ a v) * φ.1 v = φ.1 v := hφ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hinv : (infGL E 2 y)⁻¹ = infGL E 2 y⁻¹ := (map_inv (infGL E 2) y).symm
  have hfin := UpperTheory.ConvolutionTheory.R2.Fo.actFin F E D y⁻¹

  have key : ∀ a : V4 F, (∀ i, (a i).1 = 0) → D.act (infGL E 2 y⁻¹) a = a := by
    intro a ha
    let e : A F := (0, 1)
    have hea : e • a = a := by
      funext i
      apply Prod.ext
      · change (0 : _) * (a i).1 = (a i).1
        rw [ha i, mul_zero]
      · change (1 : _) * (a i).2 = (a i).2
        rw [one_mul]
    have hinf : D.act (infGL E 2 y⁻¹) a = e • D.act (infGL E 2 y⁻¹) a := by
      rw [hρ, ← Matrix.mulVec_smul, hea]
    funext i
    apply Prod.ext
    · rw [hinf, ha i]
      change (0 : _) * _ = 0
      rw [zero_mul]
    · exact congrFun (hfin a) i
  change ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
    (W.L (infGL E 2 y) φ).1 (v + a) = (W.L (infGL E 2 y) φ).1 v ∧
      ψ (B4 D.δ a v) * (W.L (infGL E 2 y) φ).1 v = (W.L (infGL E 2 y) φ).1 v
  intro a ha v
  have hfix := key a fun i => (ha i).1
  have hact : D.act (infGL E 2 y⁻¹) (v + a) = D.act (infGL E 2 y⁻¹) v + a := by
    rw [hρ, Matrix.mulVec_add, ← hρ, ← hρ, hfix]
  have hB : B4 D.δ a v = B4 D.δ a (D.act (infGL E 2 y⁻¹) v) :=
    quaternaryForm_eq_of_finitePart _ _ _ _ (fun i => (ha i).1) (hfin v).symm
  refine ⟨?_, ?_⟩
  · rw [W.L_apply, W.L_apply, hinv, hact, (hφ' a ha _).1]
  · rw [W.L_apply, hinv, mul_left_comm, hB, (hφ' a ha _).2]
