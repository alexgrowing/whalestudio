import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.OrientedChar

theorem map_inv_field {E : Type} [Field E] (τ : E →+* ℂ) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map τ)⁻¹ = G⁻¹.map τ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h),
    Matrix.map_one _ τ.map_zero τ.map_one]

theorem ringHom_map_quadrupleSum_products {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ}
    (P : Fin n → Fin n → A) (y : Fin m → Fin n → A) (Q : Fin m → Fin m → A) (x : Fin m → Fin n → A) :
    φ (∑ a, ∑ b, ∑ c, ∑ d, P a b * y c b * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, φ (P a b) * φ (y c b) * φ (Q c d) * φ (x d a) := by
  simp only [map_sum, map_mul]

theorem trace_four {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (Q : Matrix (Fin m) (Fin m) ℂ) (x : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ c, ∑ d, P a b * starRingEnd ℂ (y c b) * Q c d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

variable {D : D7}

theorem comp_hO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    θ τ (infPart D (hO S T x y)) = hAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  have hc : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = starRingEnd ℂ (((θ τ).comp (infPart D)) z) := comp_cA hθ τ
  have hg : (gramAt D S τ)⁻¹ = S.gram⁻¹.map (tauE D τ) := map_inv_field _ _ (Formalism.L2.Theta.gram_det_ne S)
  unfold hO hAt
  refine (ringHom_map_quadrupleSum_products ((θ τ).comp (infPart D)) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  rw [hg]
  refine Eq.trans ?_ (trace_four _ _ _ _).symm
  simp only [hi, hc]
  rfl

theorem valTau_symplO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    valTau θ τ (symplO S T x y) = omAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  unfold valTau symplO omAt
  rw [SymplVal.trace_AE, RingHom.map_add, RingHom.map_add, comp_cA hθ, RingHom.map_mul, RingHom.map_mul,
    comp_incA hθ, comp_hO hθ, Complex.add_re, Complex.conj_re, two_mul]

theorem finPart_cA_eq_zero {z : AE D} (hz : finPart D z = 0) : finPart D (cA D z) = 0 := by
  have h : ∀ w : AE D, finPart D (cA D w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e => rfl
  rw [h, hz, map_zero]

theorem finPart_hO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    finPart D (hO S T x y) = 0 := by
  unfold hO
  refine (ringHom_map_quadrupleSum_products (finPart D) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases h with h | h
  · have e : finPart D (x d a) = 0 := congrFun (congrFun h d) a
    rw [e, mul_zero]
  · have e : finPart D (y c b) = 0 := congrFun (congrFun h c) b
    rw [finPart_cA_eq_zero e, mul_zero, zero_mul, zero_mul]

theorem sndA_symplO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplO S T x y) = 0 := by
  have h0 : finPart D (incA D D.host.xi0 * hO S T x y) = 0 := by
    rw [RingHom.map_mul, finPart_hO S T h, mul_zero]
  have h1 : finPart D (algebraMap (AF D.host.F) (AE D) (symplO S T x y)) = 0 := by
    unfold symplO
    rw [SymplVal.trace_AE, RingHom.map_add, h0, finPart_cA_eq_zero h0, add_zero]
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F)
    (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  apply hinj
  rw [map_zero]
  exact h1

theorem char_symplOH : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) →
      ψ (symplOH S T x y) =
        Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  intro D θ ψ hθ hψ S T x y h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (real_adele_ext_and_char D θ σ hσ _ (sndA_symplO S T h)).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => valTau_symplO hθ S T τ x y] at e
  exact e

end GlobalTheory.OrientedChar
