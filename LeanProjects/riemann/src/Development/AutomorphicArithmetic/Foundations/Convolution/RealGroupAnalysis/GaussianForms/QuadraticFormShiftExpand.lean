import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_add' {F : Type} [Field F] [NumberField F] (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private lemma psi_neg_mul {F : Type} [Field F] [NumberField F] (a : A F) : ψ (-a) * ψ a = 1 := by
  rw [← psi_add', neg_add_cancel]
  simp [ψ]

private lemma quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b c : A F) (hbc : b * c = 1) (x y v : V4 F) :
    b * q4 δ (x + (y + fun i => c * v i)) = b * q4 δ (x + y) + B4 δ x v + B4 δ y v + c * q4 δ v := by
  simp only [q4, B4, Pi.add_apply]
  linear_combination (2 * ((x 2 + y 2) * v 2 - rt δ * ((x 3 + y 3) * v 3)) - (x 1 + y 1) * v 0 - (x 0 + y 0) * v 1
    + c * (v 2 ^ 2 - rt δ * v 3 ^ 2 - v 1 * v 0)) * hbc

private lemma quaternaryForm_neg_right {F : Type} [Field F] [NumberField F] (δ : F) (x v : V4 F) : B4 δ x (-v) = -B4 δ x v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.idxFt :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    ft4 δ (Pc δ (b : A F) φ.1) v = c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ft4 δ φ.1 (-v) := by
  intro F _ _ δ b c h φ v
  have hbc : (b : A F) * ((b⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv b
  let φ' : S4 F := ⟨fun x => ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x, chirpQ F δ 0 (-v) φ.1 φ.2⟩
  have hφ' : ∀ x, φ'.1 x = ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x := fun _ => rfl
  have hr : ∫ x, φ'.1 x ∂(adeleMeasurePi F) = ft4 δ φ.1 (-v) := by
    unfold ft4
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add]
    exact mul_comm _ _
  have hl : ft4 δ (Pc δ (b : A F) φ.1) v =
      ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * Lam4 δ (b : A F) φ'.1 := by
    unfold ft4 Pc Lam4 abelian₂
    rw [← integral_add_right_eq_self
      (fun y => ∫ x, φ'.1 x * ψ ((b : A F) * q4 δ (x + y)) ∂(adeleMeasurePi F))
      (fun i => ((b⁻¹ : (A F)ˣ) : A F) * v i), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add, quaternaryForm_neg_right]
    rw [quadraticForm_shift_expand δ _ _ hbc x y v, psi_add', psi_add', psi_add']
    have e1 := psi_neg_mul (B4 δ x v)
    have e2 := psi_neg_mul (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)
    linear_combination (-(φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v))
      * (ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ψ (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v))) * e1
      - (φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v)) * e2
  rw [hl, h φ', hr]
  ring
