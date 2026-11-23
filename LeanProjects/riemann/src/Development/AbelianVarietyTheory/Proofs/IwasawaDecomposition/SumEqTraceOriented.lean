import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.OrientedSmall

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace_oriented (P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a = (P * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a
      = ∑ e, ∑ b, ∑ d, P a b * c (y e b) * K e d * x d a := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ b, P a b * c (y e b) * K e d * x d a := Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_coord (J P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hP : P.map c = Pᵀ) (x y : Matrix (Fin m) (Fin n) R) :
    (P * (y.map c)ᵀ * K * x).trace = ((((y * P)ᵀ).map c)ᵀ * Jᵀ * (x * P)ᵀ * Kᵀ).trace := by
  have e1 : Jᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPJ, Matrix.transpose_one]
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_mul, hP, Matrix.transpose_mul]
  calc (P * (y.map c)ᵀ * K * x).trace
      = (P * (y.map c)ᵀ * (K * x)).trace := by simp only [Matrix.mul_assoc]
    _ = (K * x * (P * (y.map c)ᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (K * x * (P * (y.map c)ᵀ))ᵀ.trace := (Matrix.trace_transpose _).symm
    _ = (y.map c * Pᵀ * xᵀ * Kᵀ).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (y.map c * Pᵀ * (Jᵀ * Pᵀ) * xᵀ * Kᵀ).trace := by rw [e1, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem act_coord (J P g g' : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hg : (g.map c)ᵀ * J * g = J) (hgg : g * g' = 1) (x : Matrix (Fin m) (Fin n) R) :
    (h * x * g' * P)ᵀ = g.map c * (x * P)ᵀ * hᵀ := by
  have hJP : J * P = 1 := mul_eq_one_comm.1 hPJ
  have key : g' * P = P * (g.map c)ᵀ := by
    calc g' * P = (P * J) * g' * P := by rw [hPJ, Matrix.one_mul]
      _ = P * ((g.map c)ᵀ * J * g) * g' * P := by rw [hg]
      _ = P * (g.map c)ᵀ * (J * ((g * g') * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgg, Matrix.one_mul, hJP, Matrix.mul_one]
  rw [Matrix.mul_assoc (h * x), key]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Generic

variable {D : D7}

theorem cA_incA (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, incA, inclR, CMData.sig, starRingEnd_apply]

theorem gram_conjTranspose (V : HSp D) : V.gramᴴ = V.gram := by
  refine Matrix.ext fun i j => ?_
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gramInv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gramInv_map (V : HSp D) :
    ((V.gram⁻¹).map (incA D)).map (cA D) = ((V.gram⁻¹).map (incA D))ᵀ := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]
  ext i j
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [cA_incA, this]

theorem mt_mul_inv (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem hO_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    hO S T x y = hHom S T (toTWsmall S T y) (toTWsmall S T x) := by
  unfold hO hHom
  rw [if_pos hr]
  have s := sum_eq_trace (cA D) (S.gram.map (incA D)) (T.gram.map (incA D))
    (toTWsmall S T y) (toTWsmall S T x)
  have s' := sum_eq_trace_oriented (cA D) ((S.gram⁻¹).map (incA D)) (T.gram.map (incA D)) x y
  simp only [Matrix.map_apply] at s s'
  rw [s, s']
  exact trace_coord (cA D) _ _ _ (gramInv_mul S) (gramInv_map S) x y

theorem bridgeSmall (D : D7) : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · unfold symplO sympl
    rw [hO_eq S T hr]
  · unfold actHom
    rw [if_pos hr]
    exact act_coord (cA D) _ _ _ _ _ (gramInv_mul S) (mt_rel S g) (mt_mul_inv S g) x

end GlobalTheory.OrientedSmall

end
