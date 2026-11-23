import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_mulPow_fibreRank_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (G : PDivGroup p O) (k m : ℕ) :
    ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧
      RingHom.ker r = torsionIdeal O (G.A (k + m)) (p ^ k) ∧
      (∀ a, μ (r a) = mulBy O (G.A (k + m)) (p ^ m) a) ∧
      ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  obtain ⟨r, hr, hk⟩ := G.exists_res_le (m := k) (n := k + m) (by omega)
  have hle : RingHom.ker r ≤ RingHom.ker (mulBy O (G.A (k + m)) (p ^ m)) := by
    rw [hk]
    refine (kerIdeal_le_ker_iff _
      (mulBy O (G.A (k + m)) (p ^ m) : G.A (k + m) →ₐ[O] G.A (k + m))).2 fun c => ?_
    change mulBy O _ (p ^ m) (mulBy O _ (p ^ k) c) = _
    rw [mulBy_mulBy, ← pow_add, add_comm m k, mulBy_pow_self]
  let μ := liftSurj r hr (mulBy O (G.A (k + m)) (p ^ m)) hle
  have hμ : ∀ a, μ (r a) = mulBy O (G.A (k + m)) (p ^ m) a := liftSurj_apply r hr _ hle
  refine ⟨r, μ, hr, hk, hμ, fun q => ?_⟩
  obtain ⟨f, hf, hfk⟩ := G.exists_res_le (m := m) (n := k + m) (by omega)
  have hker : kerIdeal μ = RingHom.ker (f : G.A (k + m) →ₐ[O] G.A m) := by
    rw [← kerIdeal_comp_of_surjective μ hr, show μ.comp r = mulBy O (G.A (k + m)) (p ^ m) from
      BialgHom.ext hμ]
    exact hfk.symm
  have h1 := fibreDim_eq_ker_mul_range μ q
  rw [hker, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (k + m) →ₐ[O] G.A m)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    add_mul, pow_add, mul_comm (p ^ (k * G.height))] at h1
  rw [fibreDim_eq]
  have hp : 0 < p ^ (m * G.height) := pow_pos (Fact.out : p.Prime).pos _
  exact (Nat.eq_of_mul_eq_mul_left hp h1).symm

end GlobalTheory.PDivGroup
