import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockOmega

variable {D : D7}

open GlobalTheory.FockTransport

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem jm_eq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = Matrix.diagonal fun a => ((sg (ε a) : ℝ) : ℂ) := by
  rw [Formalism.REAL.Jm]
  congr 1
  funext a
  cases ε a <;> simp [sg]

theorem gramAt_inv {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) :
    (gramAt D V τ)⁻¹ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ := by
  have hP := det_fr_unit A τ
  rw [← A.fr_gram τ]
  apply Matrix.inv_eq_left_inv
  have h1 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.conjTranspose_one]
  calc (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
      = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [jm_mul_self, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem hAt_frame {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ ((B.fr τ)⁻¹ * X * A.fr τ) ((B.fr τ)⁻¹ * Y * A.fr τ) =
      (Formalism.REAL.Jm (A.ε τ) * (Yᴴ * (Formalism.REAL.Jm (B.ε τ) * X))).trace := by
  have hA := det_fr_unit A τ
  have hB := det_fr_unit B τ
  have cA : ∀ M : Matrix (Fin S.rank) (Fin S.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have cB : ∀ M : Matrix (Fin T.rank) (Fin S.rank) ℂ, ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hB, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [GlobalTheory.VacUnique.hAt, gramAt_inv A τ, ← B.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, cA, cB, Matrix.mul_nonsing_inv_cancel_left _ _ hB]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA]

theorem trace_jm {m n : ℕ} (a : Fin n → Bool) (b : Fin m → Bool) (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (Formalism.REAL.Jm a * (Yᴴ * (Formalism.REAL.Jm b * X))).trace =
      ∑ i, ∑ j, ((sg (a j) : ℝ) : ℂ) * (conj (Y i j) * (((sg (b i) : ℝ) : ℂ) * X i j)) := by
  rw [Finset.sum_comm]
  simp only [jm_eq, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, Matrix.conjTranspose_apply, RCLike.star_def]

theorem term_re (b a : Bool) (ξ z y : ℂ) (hξ : ξ.re = 0) :
    2 * (ξ * (((sg a : ℝ) : ℂ) * (conj (cf b a y) * (((sg b : ℝ) : ℂ) * cf b a z)))).re =
      -(2 * (ξ.im * (z * conj y).im)) := by
  cases a <;> cases b <;> simp [cf, sg, Complex.mul_re, Complex.mul_im, hξ] <;> ring_nf <;> simp

theorem omO_fockMat (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (Z Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S)
      (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) =
      -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  refine (GlobalTheory.VacUnique.omO_apply S T _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show GlobalTheory.VacUnique.omAt S T τ (fockMat A B τ (Z τ)) (fockMat A B τ (Y τ)) = _
  rw [GlobalTheory.VacUnique.omAt, fockMat_eq, fockMat_eq, hAt_frame, trace_jm, Formalism.IndefR.Fock.CCR.norm_embedding_hostFormConstant_eq]
  simp only [Finset.mul_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  exact term_re _ _ _ _ _ (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ)

end GlobalTheory.FockOmega
