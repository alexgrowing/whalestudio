import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem colv_latC_and_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  intro l _ P r ω hω hdet n _ _ U x y A₀ hA W₀ hW hev
  have hit : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] b = (P.φB ^ m) b := fun m b => by rw [AlgHom.coe_pow]
  have hfix : ∀ (m : ℕ) i j, P.φB^[m] ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun m i j => Function.iterate_fixed (hA i j) m
  have hφcol : ∀ (m : ℕ) c i, P.φB^[m] (colv P ω A₀ c i) =
      ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c := by
    intro m c i
    rw [hit, colv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hit, ← hit, phi_iter_kur, hfix]
  have hsum : ∀ {R : Type} [CommRing R] (f : ↥(MaximalUnramifiedExtension l) →+* R) (X : Matrix (n × Fin r) (n × Fin r) R) (m : Fin r) (i : n) c,
      ∑ k, f (fr l m (ω k)) * X (i, k) c = ((resMat n ω).map f * X) (i, m) c := by
    intro R _ f X m i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [resMat_apply, apply_ite f, ite_mul]
  have hpU : (resMat n ω).map (kd P) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
      Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR) := by
    have e : (resMat n ω).map (kd P) = ((Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
        Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) : GL (n × Fin r) P.R.BdR) :
        Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
    rw [e, U0, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rfl
  have h0 : ∀ e f, P.ιB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) e f) =
      ((U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) e f := by
    intro e f; rw [← hev]; rfl
  have hcol : ∀ (m : Fin r) c i, ev P m (colv P ω A₀ c i) =
      ∑ j, (U m : Matrix n n P.R.BdR) i j * tz P (eps x y (m, j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c := by
    intro m c i
    rw [ev, hφcol, map_sum]
    simp only [map_mul, iota_kur, h0]
    rw [hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_mul, ite_mul, mul_assoc]
  refine ⟨fun c => ⟨fun i => ?_, fun m => ⟨fun j => (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c,
    fun j => hW.1 _ _, funext fun i => ?_⟩⟩, ?_⟩
  · rw [hφcol]; simp only [hω]; rfl
  · rw [hcol]; simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
  · haveI : Nontrivial P.R.BdR := ⟨⟨(P.PD (botExt l)).ι (P.PD (botExt l)).t, 0, fun h =>
      (P.PD (botExt l)).not_mem_filtration_two (by rw [h]; exact zero_mem _)⟩⟩
    haveI : Nontrivial P.R.B := ⟨⟨1, 0, fun h => one_ne_zero (by simpa using congrArg P.ιB h : (1 : P.R.BdR) = 0)⟩⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ c, g c • colv P ω A₀ c i = 0 := fun i => by
      have := congrFun hg i; simpa [Finset.sum_apply] using this
    have hYe : ∀ i (m : Fin r) c, Ymat P ω A₀ (i, m) c = P.φB^[m] (colv P ω A₀ c i) := by
      intro i m c
      rw [hφcol, hsum, Ymat]
    have hY : (Ymat P ω A₀).mulVec (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      funext ⟨i, m⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      calc ∑ c, Ymat P ω A₀ (i, m) c * algebraMap ℚ_[l] P.R.B (g c)
          = (P.φB ^ (m : ℕ)) (∑ c, g c • colv P ω A₀ c i) := by
            rw [map_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [hYe, hit, map_smul, Algebra.smul_def, mul_comm]
        _ = 0 := by rw [hg' i, map_zero]
    have hdetY : IsUnit (Ymat P ω A₀).det := by
      rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((isUnit_det_resMat n ω hdet).map _).mul ((Matrix.isUnit_iff_isUnit_det _).1 A₀.isUnit)
    have hv0 : (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      have := congrArg (Matrix.mulVec (Ymat P ω A₀)⁻¹) hY
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetY, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    intro c
    exact (algebraMap ℚ_[l] P.R.B).injective (by simpa using congrFun hv0 c)

end GlobalTheory.PMon.ResR
