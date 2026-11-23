import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SympFrames

def sgn {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal (sgn (p := p) (q := q)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, sgn] <;> split_ifs <;> simp

theorem lineSign_eq {p q r s : ℕ} (x : Ix p q) (y : Ix r s) : lineSign x y = sgn x * sgn y := by
  rcases x with x | x <;> rcases y with y | y <;> simp [lineSign, sgn]

theorem trace_jm {p q r s : ℕ} (c c' : Matrix (Ix p q) (Ix r s) ℂ) :
    (cᵀ * Jm p q * c'.map star * (Jm r s)ᵀ).trace = ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.diagonal_transpose, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, lineSign_eq, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem quad_eq_trace {α β : Type} [Fintype α] [Fintype β]
    (U U' : Matrix α β ℂ) (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, U i j * X i k * Y j l * star (U' k l) = (Uᵀ * X * U'.map star * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frame_trace {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ}
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (a b : ℂ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (hA : Aᵀ * (a • X) * A.map star = Jm P Q) (hC : Cᵀ * (b • Y) * C.map star = Jm R S)
    (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    a * b * ((A * c * Cᵀ)ᵀ * X * (A * c' * Cᵀ).map star * Yᵀ).trace =
      ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [← trace_jm, ← hA, ← hC]
  have hm : (A * c' * Cᵀ).map star = A.map star * c'.map star * (C.map star)ᵀ := by
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C]
  simp only [Matrix.mul_assoc]
  ring

theorem symp_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (AE F E)) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, quad_eq_trace]
    exact frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFrames
