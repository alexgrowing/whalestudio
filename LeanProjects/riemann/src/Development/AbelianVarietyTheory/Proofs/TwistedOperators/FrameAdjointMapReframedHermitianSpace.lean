import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  funext i j
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    unfold frP
    simp only [Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  show S.hT (b i) (b j) = ∑ l, (∑ k, star (frP S b k i) * S.hT (S.frame k) (S.frame l)) * frP S b l j
  rw [hb i, hb j]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem inv_eq_of_gram_conjTranspose_change {n : ℕ} {K : Type} [Field K] [StarRing K] (G G' P Q : Matrix (Fin n) (Fin n) K)
    (hG : G' = Pᴴ * G * P) (hQP : Q * P = 1) (hPQ : P * Q = 1) : G'⁻¹ = Q * G⁻¹ * Qᴴ := by
  have h1 : P⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have h2 : (Pᴴ)⁻¹ = Qᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]

theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram⁻¹ = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ :=
  inv_eq_of_gram_conjTranspose_change (n := S.rank) S.gram (reS S b).gram (frP S b) (frPinv S b) (gram_reS S b)
    (frPinv_mul_frP S b) (frameMatrix_mul_frameMatrixInv S b)

end GlobalTheory.AdSpan.ReVec.FrMap

theorem GlobalTheory.AdSpan.ReVec.FrMap.cA_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem map_eToEAf_eq (n m : ℕ) (M : Matrix (Fin n) (Fin m) D.host.E) :
    M.map (eToEAf D) = (M.map (incA D)).map (toEAf D) := by
  funext i j; rfl

theorem complex_units_mul_eq_one_of_mul_eq_one {R : Type} [Ring R] {n m : ℕ} (B Pf : Matrix (Fin n) (Fin n) R) (M' M : Matrix (Fin n) (Fin m) R)
    (C : Matrix (Fin m) (Fin m) R) (h : Pf * M' = M) : B * Pf * M' * C = B * M * C := by
  rw [Matrix.mul_assoc B, h]

theorem frP_mul_adj_finPart (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Gi : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hGi : Gi = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ) :
    HMul.hMul ((frP S b).map (eToEAf D))
      ((HMul.hMul (HMul.hMul (Gi.map (incA D))
        (x.map (cA D)).transpose) (T.gram.map (incA D))).map (toEAf D)) =
    (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
        ((HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))).map (cA D)).transpose)
        (T.gram.map (incA D))).map (toEAf D) := by
  rw [map_eToEAf_eq, ← Matrix.map_mul]
  congr 1
  have e1 := Matrix.map_mul (L := x) (M := (frPinv S b).map (incA D)) (f := cA D)
  have e2 : (frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ).map (incA D) =
      (frPinv S b).map (incA D) * (S.gram⁻¹).map (incA D) * ((frPinv S b)ᴴ).map (incA D) := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have e4 : (((frPinv S b).map (incA D)).map (cA D))ᵀ = ((frPinv S b)ᴴ).map (incA D) := by
    funext i j
    exact cA_incA_star _
  have h5 : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
    rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e1, hGi, e2, Matrix.transpose_mul, e4]
  simp only [← Matrix.mul_assoc]
  simp only [h5, Matrix.one_mul]

theorem frMapAdj_reS (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T) :
    frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := by
  have h1 : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val * (frP S b).map (eToEAf D) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val]
  unfold frMapAdj reW
  erw [h1]
  exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ (frP_mul_adj_finPart S T b x _ (gram_reS_inv S b))

end GlobalTheory.AdSpan.ReVec.FrMap
