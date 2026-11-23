import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem substF_invT_minor_det {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} (X : Data P)
    (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ) (τ : D.what₂.Tau) (s : Fin P.a → Fin P.d) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det) =
      MvPolynomial.C ((G τ)⁻¹.det) * MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det := by
  set M := Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)
  set φ := GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
  set H : Matrix (Fin P.a) (Fin P.a) (MvPolynomial (FVar D X.B.rank X.A.rank) ℂ) :=
    Matrix.of fun i'' i' => MvPolynomial.C ((G τ)⁻¹ (Fin.cast X.rkA.symm i') (Fin.cast X.rkA.symm i''))
  have hH : H.det = MvPolynomial.C ((G τ)⁻¹.det) := by
    have e1 : H = (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D X.B.rank X.A.rank) ℂ).mapMatrix
        (((G τ)⁻¹.transpose).submatrix (finCongr X.rkA.symm) (finCongr X.rkA.symm)) := by
      ext i j; simp [H]
    rw [e1, ← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hM : ((φ.comp (MvPolynomial.rename X.var)).mapMatrix M) = (MvPolynomial.rename X.var).mapMatrix M * H := by
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, M, H, Matrix.of_apply, AlgHom.comp_apply,
      MvPolynomial.rename_X, φ, GlobalTheory.CompactHowe.substF_X, Data.var]
    rw [Finset.sum_eq_single (Fin.cast X.rkB.symm (s i))]
    · simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
      exact Fintype.sum_equiv (finCongr X.rkA) _ _ (fun l => by simp [mul_comm])
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  have := AlgHom.map_det (φ.comp (MvPolynomial.rename X.var)) M
  rw [AlgHom.comp_apply] at this
  rw [this, hM, Matrix.det_mul, hH, ← AlgHom.map_det, mul_comm]

end GlobalTheory.NormDict

namespace GlobalTheory.NormDict

theorem substF_invT_minorPol : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  intro D cc δ t0 Q P X T G
  rw [minorPol, map_prod, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  simp only [substF_invT_minor_det, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

end GlobalTheory.NormDict
