import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocFamPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fam_eq_L_pf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    L (a s) (fP 1) = fun v => fam d.m X s v := by
  obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := diagonal fun j => (Real.exp (s * X j) : ℂ) with hA
  have hdet : A.det = ((Real.exp (∑ j, s * X j) : ℝ) : ℂ) := by
    rw [hA, det_diagonal, Real.exp_sum, Complex.ofReal_prod]
  have hpos : 0 < Real.exp (∑ j, s * X j) := Real.exp_pos _
  have hunit : IsUnit A.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hinv : (Aᴴ)⁻¹ = diagonal fun j => (Real.exp (-(s * X j)) : ℂ) := by
    rw [hA, diagonal_conjTranspose]
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hy : mR (a s) = mLoc A := by
    rw [show mR (a s) = _ from ha s, mLoc, hinv]
  rw [hk (a s) A hunit hy (fP 1) (hFP d.m d.n 1)]
  funext v
  have hn : ‖A.det‖ = Real.exp (∑ j, s * X j) := by
    rw [hdet, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hn, ← hdet, div_self hunit.ne_zero, _root_.one_zpow, one_mul, hdet]
  simp only [fam, fP, evX, map_one, one_mul, gs]
  congr 1
  · rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · congr 1
    push_cast
    rw [neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
    have he : (Matrix.of v * A) b j = v b j * ((Real.exp (s * X j) : ℝ) : ℂ) := by
      rw [hA, Matrix.mul_diagonal]
      rfl
    erw [he]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.ofReal_mul, mul_pow,
      Complex.ofReal_exp, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
theorem fam_eq_L_closed_k : type_of% @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k := @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
