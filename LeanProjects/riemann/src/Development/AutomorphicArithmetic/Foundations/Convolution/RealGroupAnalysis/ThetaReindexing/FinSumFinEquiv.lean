import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierCoordinates
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi F (Fin 4)) (a b : A F) :
    (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) ∈ schwartzBruhatPi F (Fin 2) := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  let M : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id e
  let N : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix e id
  have hNM : N * M = 1 := by
    ext i j
    simp [M, N, Matrix.mul_apply, Matrix.one_apply]
  have hMN : M * N = 1 := by
    ext i j
    have h := Equiv.sum_comp e
      (fun k => (1 : Matrix (Fin 4) (Fin 4) F) i k * (1 : Matrix (Fin 4) (Fin 4) F) k j)
    rw [Matrix.mul_apply]
    refine h.trans ?_
    simp [Matrix.one_apply]
  have hv : ∀ x : Fin 2 ⊕ Fin 2 → A F, M.map (algebraMap F (A F)) *ᵥ x = fun i => x (e.symm i) := by
    intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp e.symm]
    simp [Matrix.one_apply, apply_ite]
  have h1 := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hf
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![a, b]
  have h3 : (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) =
      fun x : Fin 2 → A F => f (M.map (algebraMap F (A F)) *ᵥ Sum.elim ![a, b] x) := by
    funext z
    rw [hv]
    congr 1
    funext i
    fin_cases i <;> simp [e, finSumFinEquiv] <;> rfl
  rw [h3]
  exact h2

private def scaleEquiv {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    (Fin 2 → F) ≃ (Fin 2 → F) where
  toFun ξ := ![2 * ξ 0, -2 * δ * ξ 1]
  invFun ξ := ![ξ 0 / 2, -(ξ 1) / (2 * δ)]
  left_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  right_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp

end UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

open UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv in
theorem UpperTheory.ConvolutionTheory.R2.D.rowW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (r₀ r₁ : F) φ, ThRow (rt r₀) (rt r₁) (W.Om (wW F) φ).1 = ThRow (rt (-r₁)) (rt r₀) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W r₀ r₁ φ
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hb : D.b 1 = 0 := by rw [D.b1, hθ]
    exact D.b.ne_zero 1 hb
  have hS : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  set G : (Fin 2 → A F) → ℂ := fun z => hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] with hGdef
  have hG : G ∈ schwartzBruhatPi F (Fin 2) :=
    slice_mem (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1 (-rt r₁) (rt r₀)
  have hR : ThRow (rt (-r₁)) (rt r₀) φ.1 = ∑' ξ : Fin 2 → F, G fun i => algebraMap F (A F) (ξ i) := by
    simp only [ThRow, hGdef, map_neg]
  rw [hR, tsum_algebraMap_eq_tsum_adelicFourierPi hG,
    ← (scaleEquiv D.δ hδ).tsum_eq (fun ξ : Fin 2 → F => adelicFourierPi F G fun i => algebraMap F (A F) (ξ i))]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [hS, UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ _ hδ]
  simp only [adelicFourierPi, Fin.sum_univ_two]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hGdef, ψ, scaleEquiv, Equiv.coe_fn_mk]
  have key : 2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1))) =
      z 0 * algebraMap F (A F) (2 * ξ 0) + z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1) := by
    simp only [rt, map_mul, map_neg, map_ofNat]
    ring
  show hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1)))) : Circle) : ℂ) =
    hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (z 0 * algebraMap F (A F) (2 * ξ 0) +
        z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1)) : Circle) : ℂ)
  rw [key]
