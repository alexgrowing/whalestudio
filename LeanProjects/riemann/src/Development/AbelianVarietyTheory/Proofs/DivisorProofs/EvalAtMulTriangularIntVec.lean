import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem intVec_mem_nabla {n : ℕ} (la : Fin n → ℕ) (i : Idx la) : intVec la i ∈ nabla la ℤ := by
  have h := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.1.2.1
  rw [nabla, ← h]
  exact Submodule.subset_span ⟨i, rfl⟩

def genUpperTri (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  Matrix.of fun i j => if i ≤ j then X (i, j) else 0

theorem genUpperTri_blockTriangular (n : ℕ) : (genUpperTri n).BlockTriangular id := by
  intro i j hij
  simp only [genUpperTri, Matrix.of_apply]
  rw [if_neg (not_le.mpr (show j < i from hij))]

theorem colAct_intCast_of_mem {n : ℕ} {la : Fin n → ℕ} {f : Pol n ℤ} (hf : f ∈ nabla la ℤ)
    {S : Type} [CommRing S] (b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    colAct b (map (Int.castRingHom S) f) = diagChar la b • map (Int.castRingHom S) f := by
  let ψ : MvPolynomial (Fin n × Fin n) ℤ →+* S := (aeval (R := ℤ) fun v : Fin n × Fin n => b v.1 v.2).toRingHom
  have hB : (genUpperTri n).map ψ = b := by
    ext i j
    simp only [Matrix.map_apply, genUpperTri, Matrix.of_apply]
    split_ifs with h
    · simp [ψ]
    · rw [map_zero, hb (show id j < id i from not_le.mp h)]
  have hgen := colAct_map_of_mem (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) hf (genUpperTri n)
    (genUpperTri_blockTriangular n)
  have h2 := congrArg (map ψ) hgen
  rw [map_colAct, hB, map_map] at h2
  have hc : ψ.comp (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) = Int.castRingHom S :=
    RingHom.ext_int _ _
  rw [hc] at h2
  rw [h2, smul_eq_C_mul, map_mul, map_C, map_map, hc, smul_eq_C_mul]
  congr 2
  simp only [diagChar, map_prod, map_pow, ← hB, Matrix.map_apply]

theorem evalAt_mul_triangular_intVec {n : ℕ} (la : Fin n → ℕ) (i : Idx la) {S : Type} [CommRing S]
    (y b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    DualWeyl.evalAt (y * b) (map (Int.castRingHom S) (intVec la i)) =
      diagChar la b * DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  rw [← evalAt_colAct, colAct_intCast_of_mem (intVec_mem_nabla la i) b hb, smul_eq_C_mul, map_mul]
  simp [DualWeyl.evalAt]

theorem tval_mul_triangular : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (S : Type) [CommRing S] (x : TIdx la → S) (y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), (∀ t, (b t).BlockTriangular id) → tval la x (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * tval la x y := by
  intro T _ _ N la S _ x y b hb
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [evalAt_mul_triangular_intVec _ _ _ _ (hb _), Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
