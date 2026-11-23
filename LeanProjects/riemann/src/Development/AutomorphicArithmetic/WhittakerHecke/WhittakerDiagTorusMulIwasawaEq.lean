import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sc_val {R : Type} [CommRing R] (z : Rˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z).val = Matrix.diagonal fun _ => (z : R) := rfl

private theorem aE_nU (y : (A ℚ)ˣ) (b : A ℚ) :
    aE y * gl (nU b) = gl (nU ((y : A ℚ) * b)) * aE y := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, gl_val]
  fin_cases i <;> fin_cases j <;> simp [aE, nU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem aE_mD (y ζ : (A ℚ)ˣ) :
    aE y * gl (mD ζ) = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * aE (y * ζ ^ 2) := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, sc_val]
  have hz : ((ζ⁻¹ : (A ℚ)ˣ) : A ℚ) * (ζ : A ℚ) = 1 := Units.inv_mul ζ
  fin_cases i <;> fin_cases j <;> simp [aE, mD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  linear_combination (-(y : A ℚ) * (ζ : A ℚ)) * hz

private theorem em_nU {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (x : A ℚ) :
    em E (gl (nU x)) = nE D ![x, 0] := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, nE, Matrix.GeneralLinearGroup.map_apply, gl_val]
  fin_cases i <;> fin_cases j <;> simp [nU, Dat.mkE]

private theorem em_sc {E : Type} [Field E] [NumberField E] (z : (A ℚ)ˣ) :
    em E (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E z) := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply, sc_val, coe_ideleEmbedding]
  by_cases e : i = j <;> simp [e, Matrix.diagonal]

private theorem Wo_lev {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} {N : ℕ}
    (hl : ∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) {κ : GL (Fin 2) (A ℚ)} (hκ : Lev N κ) (h : GL (Fin 2) (A E)) :
    Wo D φ (h * em E κ) = Wo D φ h := by
  unfold Wo
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only []
  rw [← mul_assoc, hl κ hκ]

theorem UpperTheory.whittaker_diagTorus_mul_iwasawa_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (N : ℕ), (∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) → ∀ (y ζ : (A ℚ)ˣ) (b : A ℚ) (r κ : GL (Fin 2) (A ℚ)), Lev N κ →
          Wo D φ (em E (aE y * (gl (nU b) * gl (mD ζ) * r * κ))) = ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 * Wo D φ (em E (aE (y * ζ ^ 2) * r)) := by
  intro E _ _ D ω φ hφ N hl y ζ b r κ hκ
  obtain ⟨-, -, hn, hz⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hφ
  have e : aE y * (gl (nU b) * gl (mD ζ) * r * κ) =
      gl (nU ((y : A ℚ) * b)) * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * (aE (y * ζ ^ 2) * r)) * κ := by
    calc aE y * (gl (nU b) * gl (mD ζ) * r * κ) = (aE y * gl (nU b)) * gl (mD ζ) * r * κ := by
          simp only [mul_assoc]
      _ = gl (nU ((y : A ℚ) * b)) * (aE y * gl (mD ζ)) * r * κ := by
          rw [aE_nU]; simp only [mul_assoc]
      _ = _ := by rw [aE_mD]; simp only [mul_assoc]
  have hN : ideleNorm ℚ E (ideleEmbedding ℚ E ζ⁻¹) = ζ⁻¹ ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  rw [e, map_mul, Wo_lev D hl hκ, map_mul, map_mul, em_nU D, em_sc, hn, hz, hN, map_pow]
  simp
