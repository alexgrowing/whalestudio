import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel

variable {D : D7}

theorem gram_det_ne_zero (S : HSp D) : S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv0
  set x : S.V := ∑ j, v j • S.frame j with hxdef
  have hfr : ∀ i, S.hT (S.frame i) x = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [hxdef, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Formalism.BasicNotions.HSpace.gram, mul_comm]
  have hx : S.hT.flip x = 0 := S.frame.ext fun i => by simpa using hfr i
  have hx0 : x = 0 := S.nondeg.2 x fun y => by
    have := LinearMap.congr_fun hx y
    simpa using this
  funext j
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hx0 j

theorem isUnit_det_incM (S : HSp D) (c : D.host.E) (hc : c ≠ 0) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det := by
  have h1 : (c • S.gram).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (gram_det_ne_zero S)
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) (c • S.gram).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact (isUnit_iff_ne_zero.2 h1).map _

variable {R : Type} [CommRing R]

def coordsEquiv {n m d : ℕ} (e : Fin m ≃ Fin d) (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    Matrix (Fin n) (Fin d) R ≃+ Matrix (Fin m) (Fin n) R where
  toFun u := uᵀ.submatrix e id * G
  invFun x := ((x * G⁻¹).submatrix e.symm id)ᵀ
  left_inv u := by
    dsimp only
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hG, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Function.comp_id, Matrix.submatrix_id_id, Matrix.transpose_transpose]
  right_inv x := by
    dsimp only
    rw [Matrix.transpose_transpose, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
      Matrix.submatrix_id_id, Matrix.nonsing_inv_mul_cancel_right _ _ hG]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e id * G = uᵀ.submatrix e id * G + vᵀ.submatrix e id * G
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl

theorem coords (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E) (hc : c ≠ 0) :
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) :=
  ⟨coordsEquiv e _ (isUnit_det_incM S c hc), fun _ => rfl⟩

end GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel
