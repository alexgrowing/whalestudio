import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matRep_of :
    MatRep := by
  intro R S _ _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R S
  set e : Fin n → S := fun k => f (Pi.single k 1) with he
  have hsum : ∀ s : S, ∑ k, g s k • e k = s := by
    intro s
    have h1 : f (g s) = s := LinearMap.congr_fun hfg s
    conv_rhs => rw [← h1, pi_eq_sum_univ (g s)]
    simp only [map_sum, map_smul, e]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨n, fun s => Matrix.of fun j k => g (s * e k) j, ?_⟩
  intro B _ _ I _ _ z hz
  let φ := AlgEquiv.ofBijective (splitMap z) hz
  let G : Fin n → (B ⊗[R] S →ₗ[B] B) := fun j =>
    (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ ((LinearMap.proj j ∘ₗ g).baseChange B)
  have hG : ∀ j b s, G j (b ⊗ₜ s) = algebraMap R B (g s j) * b := by
    intro j b s
    simp [G, LinearMap.baseChange_tmul, Algebra.smul_def]
  have hK : ∀ x i, ∑ k, z i (e k) * G k x = splitMap z x i := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [splitMap_tmul]
      simp only [hG]
      conv_rhs => rw [← hsum s]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Algebra.smul_def]
      ring
    | add x y hx hy =>
      simp only [map_add, mul_add, Finset.sum_add_distrib, hx, hy, Pi.add_apply]
  have hL : ∀ t : S, ∑ i, z i t • φ.symm (Pi.single i 1) = (1 : B) ⊗ₜ t := by
    intro t
    apply φ.injective
    rw [map_sum]
    simp only [map_smul, AlgEquiv.apply_symm_apply]
    funext i'
    simp [φ, splitMap_tmul, Finset.sum_apply, Pi.single_apply]
    show (z i') t = splitMap z (1 ⊗ₜ t) i'
    rw [splitMap_tmul, one_mul]
  refine ⟨Matrix.of fun i k => z i (e k), Matrix.of fun j i => G j (φ.symm (Pi.single i 1)), ?_, ?_⟩
  · ext i i'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [hK]
    have h2 : splitMap z (φ.symm (Pi.single i' 1)) = Pi.single i' 1 := φ.apply_symm_apply _
    rw [h2, Matrix.one_apply, Pi.single_apply]
  · intro s
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.map_apply]
    have h3 : (algebraMap R B) (g (s * e k) j) = G j ((1 : B) ⊗ₜ (s * e k)) := by
      rw [hG, mul_one]
    rw [h3, ← hL, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
