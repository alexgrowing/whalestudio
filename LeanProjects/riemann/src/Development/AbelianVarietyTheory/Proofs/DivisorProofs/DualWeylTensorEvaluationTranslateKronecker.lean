import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem evalAt_mul_intVec {n : ℕ} (la : Fin n → ℕ) {K S : Type} [Field K] [CharZero K] [CommRing S] (φ : K →+* S)
    (g : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) S) (j : Idx la) :
    GlobalTheory.DualWeyl.evalAt (g.map φ * y) (map (Int.castRingHom S) (intVec la j)) =
      ∑ i, φ (rhoMat la g i j) * GlobalTheory.DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  have h1 : (rho la K gᵀ (basis la K j) : Pol n K) = ∑ i, rhoMat la g i j • (basis la K i : Pol n K) := by
    have h := (basis la K).sum_repr (rho la K gᵀ (basis la K j))
    conv_lhs => rw [← h]
    simp only [Submodule.coe_sum, Submodule.coe_smul, rhoMat, LinearMap.toMatrix_apply]
  have hmap : ∀ i, map φ (basis la K i : Pol n K) = map (Int.castRingHom S) (intVec la i) := by
    intro i
    rw [coe_basis, map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom S)]
  rw [coe_rho, Matrix.transpose_transpose] at h1
  rw [← hmap j, ← evalAt_rowAct, ← GlobalTheory.NabStab.map_rowAct, coe_basis, ← coe_basis, h1]
  simp only [map_sum, map_smul, smul_eq_C_mul, map_mul, map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmap i]
  simp [GlobalTheory.DualWeyl.evalAt]

theorem tval_translate : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  intro T _ _ N la K S _ _ _ φ x g y
  unfold tval
  simp only [evalAt_mul_intVec, Finset.prod_univ_sum]
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
