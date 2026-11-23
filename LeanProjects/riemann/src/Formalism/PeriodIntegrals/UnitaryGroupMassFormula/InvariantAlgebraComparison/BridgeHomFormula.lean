import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantAlgebraComparison.InvAlgOfSteps

noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem hmat_mul (I : AutInst) (g h : HAd I) : hmat I (g * h) = hmat I g * hmat I h := rfl

theorem hmat_one (I : AutInst) : hmat I 1 = 1 := rfl

theorem P_mul_inv (I : AutInst) (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem P_inv_mul (I : AutInst) (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem ofHAInf_mul (I : AutInst) (g h : HAd I) (v : InfinitePlace I.F) :
    ofHAInf I (g * h) v = ofHAInf I g v * ofHAInf I h v := by
  unfold ofHAInf
  rw [hmat_mul, Matrix.map_mul]
  set A := (hmat I g).map (thetaV I v)
  set B := (hmat I h).map (thetaV I v)
  set P := I.P v
  calc P⁻¹ * (A * B) * P = P⁻¹ * A * (P * P⁻¹) * B * P := by
        rw [P_mul_inv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = P⁻¹ * A * P * (P⁻¹ * B * P) := by simp only [Matrix.mul_assoc]

theorem ofHAInf_one (I : AutInst) (v : InfinitePlace I.F) : ofHAInf I 1 v = 1 := by
  unfold ofHAInf
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, P_inv_mul]

theorem ofHAFin_mul (I : AutInst) (g h : HAd I) :
    ofHAFin I (g * h) = ofHAFin I g * ofHAFin I h := by
  unfold ofHAFin
  rw [hmat_mul, Matrix.map_mul]

theorem ofHAFin_one (I : AutInst) : ofHAFin I 1 = 1 := by
  unfold ofHAFin
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _)]

def infU (I : AutInst) (h : HAd I) (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨ofHAInf I h v, ofHAInf I h⁻¹ v,
    by rw [← ofHAInf_mul, mul_inv_cancel, ofHAInf_one],
    by rw [← ofHAInf_mul, inv_mul_cancel, ofHAInf_one]⟩, ofHAInf_mem I h v⟩

def finU (I : AutInst) (h : HAd I) : I.Gf :=
  ⟨⟨ofHAFin I h, ofHAFin I h⁻¹,
    by rw [← ofHAFin_mul, mul_inv_cancel, ofHAFin_one],
    by rw [← ofHAFin_mul, inv_mul_cancel, ofHAFin_one]⟩, ofHAFin_mem I h⟩

def bridgeHom (I : AutInst) : HAd I →* I.GA where
  toFun h := (fun v => infU I h v, finU I h)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_one I v))
    · exact Subtype.ext (Units.ext (ofHAFin_one I))
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_mul I g h v))
    · exact Subtype.ext (Units.ext (ofHAFin_mul I g h))

end PI.UnitaryGroupMassFormula.BridgeInvAlg
