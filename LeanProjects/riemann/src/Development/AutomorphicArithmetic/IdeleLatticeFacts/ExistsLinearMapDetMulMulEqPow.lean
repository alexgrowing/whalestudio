import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.exists_linearMap_det_mul_mul_eq_pow :
    ∀ {K : Type} [Field K] {m n : ℕ} (H : Matrix (Fin m) (Fin m) K) (G : Matrix (Fin n) (Fin n) K),
        ∃ T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K, (∀ u, T u = H * u * G) ∧
          LinearMap.det T = H.det ^ n * G.det ^ m := by
  intro K _ m n H G
  let T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K :=
    { toFun := fun u => H * u * G
      map_add' := by
        intro u v
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c u
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨T, fun u => rfl, ?_⟩
  have hrepr : ∀ (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n),
      (Matrix.stdBasis K (Fin m) (Fin n)).repr M (i, j) = M i j := by
    intro M i j
    simp [Matrix.stdBasis]
  have hmat : LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) T
      = H ⊗ₖ Gᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, hrepr]
    simp [T, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq', Finset.sum_ite_eq, ite_mul]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), hmat, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]
