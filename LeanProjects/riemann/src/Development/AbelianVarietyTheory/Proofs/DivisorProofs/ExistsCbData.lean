import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsCB

theorem exists_cbData : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (m : ℕ) (c : Fin (m + 1) → ℕ) (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) (t : Fin m → InfinitePlace K → ℝ), (∀ i v, IsUnit (Xc i v).det) → (∀ j v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v ((Kj j).mulVec x) ^ 2 ≤ Real.exp (t j v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) v x ^ 2) → ∃ cb : CBData Xc Kj, ∀ j v, Real.log (cb.sq j v) ≤ t j v := by
  intro K _ _ _ _ m c Xc Kj t hX h
  refine ⟨{
    AA := fun _ => Unit
    Cl := fun _ _ => Unit
    W := fun i _ => EuclideanSpace ℂ (Fin (c i))
    γ := fun _ _ => 1
    Φ := fun i v x _ => WithLp.toLp 2 ((Xc i v)⁻¹.mulVec x)
    ε := fun _ _ _ _ => 1
    T := fun j v _ _ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v))
    hcl := fun _ => 1
    tmax := fun j v => Real.exp (t j v)
    hyp := ⟨hX, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_,
      fun _ _ => (Real.exp_pos _).le, fun _ _ => by simp⟩ }, ?_⟩
  · intro i v x
    rw [Formalism.DivisionValues.fnorm, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    simp
  · intro j v x
    funext q
    simp only [Formalism.DimensionVariation.liftOp, Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
      mul_one, one_smul, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX _ v), Matrix.mul_one]
  · intro j v _ _
    have key := Formalism.BasicNotions.opNormAt_sq_le (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (hX _) v (IsTotallyComplex.isComplex v)
      (Matrix.mulVecLin (Kj j)) (Real.exp (t j v)) (Real.exp_pos _).le (fun x => by
        rw [← Formalism.BasicNotions.normAt_sq_eq_majAt, ← Formalism.BasicNotions.normAt_sq_eq_majAt]
        exact h j v x)
    have hm : LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
        (Matrix.mulVecLin (Kj j)) = Kj j := by
      ext a b
      simp [LinearMap.toMatrix_apply]
    have e : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((Xc j.succ v)⁻¹ *
          (LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
            (Matrix.mulVecLin (Kj j))).map v.embedding * Xc j.castSucc v))‖ := rfl
    rw [e, hm] at key
    exact key
  · intro j v
    show Real.log (Formalism.DimensionVariation.cbSq (Fintype.card Unit) (Fintype.card Unit) 1 1 (Real.exp (t j v))) ≤ t j v
    simp [Formalism.DimensionVariation.cbSq]

end GlobalTheory.DefRowsCB
