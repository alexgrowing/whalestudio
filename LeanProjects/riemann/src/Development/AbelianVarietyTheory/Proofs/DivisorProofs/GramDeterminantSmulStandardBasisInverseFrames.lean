import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem GlobalTheory.DefPt.det_gramPl_smul_single : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  intro K _ _ _ ι _ _ n eqv Y hY t v
  have hinv : ((Y v.embedding)⁻¹)⁻¹ = Y v.embedding :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hY _))
  have hf : ∀ a : ι, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (t • (Pi.single a 1 : ι → K)) = fun i => v.embedding t * Y v.embedding i a := by
    intro a
    funext i
    simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, hinv, Matrix.mulVec, dotProduct, Pi.basisFun_repr,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hg : Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K)) =
      ((‖v.embedding t‖ ^ 2 : ℝ) : ℂ) • Matrix.reindex eqv eqv ((Y v.embedding)ᴴ * Y v.embedding) := by
    ext a b
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, Matrix.of_apply, Matrix.smul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (v.embedding t)
    push_cast
    rw [← this]
    simp only [RCLike.star_def]
    ring
  rw [hg, Matrix.det_smul, Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← pow_mul]
