import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly

noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem rep_sg_succ (σ : R ≃ₐ[k] R) (i : ℕ) (d : GL (Fin n) R) :
    sg (σ ^ (i + 1)) d = sg σ (sg (σ ^ i) d) := by
  ext a b
  simp [sg, pow_succ', Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_one (d : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) d = d := by
  ext a b
  simp [sg, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_nm_succ (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ (q + 1) d = nm σ q d * sg (σ ^ q) d := by
  simp [nm, List.range_succ]

private theorem rep_shift (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    d * sg σ (nm σ q d) = nm σ q d * sg (σ ^ q) d := by
  induction q with
  | zero => simp [nm, rep_sg_one]
  | succ q ih => rw [rep_nm_succ, map_mul, ← mul_assoc, ih, rep_sg_succ]

private theorem rep_cp_up (γ : GL (Fin n) k) : cp (up R γ) = (cp γ).map (algebraMap k R) := by
  rw [cp, cp, ← Matrix.charpoly_map]
  rfl

end

theorem nmRep : NmRep := by
  intro k R _ _ _ _ σ q hσ n δ γ hsep hcp
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((nm σ q δ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rwa [← hcp] at h
  obtain ⟨x, hx⟩ := (conjSep k R n _ hs).1 ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
    ((rep_cp_up γ).trans hcp.symm)
  have hx' : nm σ q δ * x = x * up R γ := Units.ext (by simpa using hx)
  have h1 : nm σ q (sgConj σ x δ) = up R γ := by
    rw [(nmPoly k R σ q hσ n δ).2 x, mul_assoc, hx', inv_mul_cancel_left]
  refine ⟨x, h1, ?_⟩
  have h2 := rep_shift σ q (sgConj σ x δ)
  rw [h1, rep_sg_up, hσ.pow, rep_sg_one] at h2
  exact h2

end UpperTheory.ConvolutionTheory.D
