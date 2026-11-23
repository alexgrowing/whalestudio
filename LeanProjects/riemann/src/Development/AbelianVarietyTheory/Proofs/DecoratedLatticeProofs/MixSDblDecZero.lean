import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

abbrev zeroSp (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 0

def stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) : Matrix (Fin (a + a)) (Fin k) D.host.E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stackRows_gram (A : HSp D) {k l : ℕ} (X Y : Matrix (Fin A.rank) (Fin k) D.host.E)
    (P Q : Matrix (Fin A.rank) (Fin l) D.host.E) :
    (stackRows X Y)ᴴ * (dblSp A).gram * stackRows P Q = Xᴴ * A.gram * P - Yᴴ * A.gram * Q := by
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, stackRows,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

def dblDec (A : HSp D) : HypDec (dblSp A) (zeroSp D) A.rank where
  e := stackRows A.gram⁻¹ A.gram⁻¹
  e' := stackRows ((2 : D.host.E)⁻¹ • 1) (-((2 : D.host.E)⁻¹ • 1))
  i₀ := 0
  ee := by rw [stackRows_gram, sub_self]
  e'e' := by
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_self]
  e'e := by
    have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_assoc,
      mul_nonsing_inv _ hG, Matrix.mul_one, conjTranspose_smul, conjTranspose_one, ← add_smul, star_inv₀, star_ofNat]
    rw [show ((2 : D.host.E)⁻¹ + 2⁻¹) = 1 by rw [← two_mul, mul_inv_cancel₀ two_ne_zero], one_smul]
  iso := Matrix.ext fun i _ => Fin.elim0 i
  i₀e := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  i₀e' := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  rank_add := by show 0 + 2 * A.rank = A.rank + A.rank; omega

theorem dblDec_qY (A : HSp D) :
    (dblDec A).qY = (Matrix.fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (-1)).submatrix id
      finSumFinEquiv.symm := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [HypDec.qY]
  show (stackRows A.gram⁻¹ A.gram⁻¹)ᴴ * (dblSp A).gram = _
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, conjTranspose_submatrix,
    submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    conjTranspose_nonsing_inv, gram_conjTranspose, nonsing_inv_mul _ hG]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, nonsing_inv_mul _ hG]

theorem extY_dblDec (A B : HSp D) (w : Mx D B.rank A.rank) : (dblDec A).extY B w = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w := by
  rw [HypDec.extY_apply, HypDec.pY, dblDec_qY]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, rat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Matrix.submatrix_apply,
    id, Equiv.symm_apply_apply]
  rcases s with k | k
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

theorem mixS_dblDec_zero (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (f : WO (dblSp A) B → ℂ) (w₀ : WO (zeroSp D) B) :
    (dblDec A).mixS B ψ ν 𝓕 f 0 w₀ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero A B ν 𝓕 f := by
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  have hz : ∀ y : WO (dblSp A) B, symplOH (dblSp A) B y 0 = 0 := fun y => by
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := dblSp A) (T := B) y 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  unfold HypDec.mixS GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  congr 1
  funext a
  rw [HypDec.integrandS_eq, map_zero, map_zero, hz, AddChar.map_zero_eq_one, one_mul, add_zero, add_zero,
    extY_dblDec]

end GlobalTheory.Core.Rk.SWLaw
