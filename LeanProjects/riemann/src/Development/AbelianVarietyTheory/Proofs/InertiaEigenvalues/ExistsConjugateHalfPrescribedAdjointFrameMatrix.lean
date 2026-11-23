import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.AdjHalfLift

open GlobalTheory.AdelicLatMove

theorem gramInv_mul_gram {D : D7} (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem cF_cF {D : D7} (w : EAf D) : cF D (cF D w) = w := by
  obtain ⟨Z, -, rfl⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) w
  exact GlobalTheory.PlaceVec.cF_cF_toEAf Z

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_half_frMapAdj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  intro D S T βS βT e hee z hz
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
    HMul.hMul (HMul.hMul (HMul.hMul (S.gram.map (eToEAf D)) βS.val) z) (HMul.hMul (βT⁻¹).val ((T.gram⁻¹).map (eToEAf D)))
  let X : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => cF D (N j i)
  refine ⟨Matrix.of fun i j => cA D e * L (X i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, ← map_mul, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hcc : cF D (toEAf D (cA D e)) = toEAf D e := by
      rw [← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]
    have hY : (((Matrix.of fun i j => cA D e * L (X i j) : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D e • N := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hL, X, cF_cF, hcc,
        Matrix.smul_apply, smul_eq_mul]
    rw [GlobalTheory.PlaceVec.frMapAdj_eq, hY, Matrix.mul_smul, Matrix.smul_mul]
    have e1 : HMul.hMul (HMul.hMul (HMul.hMul (βS⁻¹).val ((S.gram⁻¹).map (eToEAf D))) N)
        (HMul.hMul (T.gram.map (eToEAf D)) βT.val) = z :=
      GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ z (gramInv_mul_gram S) (Units.inv_mul βS)
        (gramInv_mul_gram T) (Units.inv_mul βT)
    rw [e1]
    exact Matrix.ext fun i j => hz i j

end GlobalTheory.AdjHalfLift
