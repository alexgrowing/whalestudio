import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearMapFibreRankSplitCompSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroupStatement
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.TorsDim

theorem fibreDim_quot_torsionIdeal : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ), 1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B] [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B), (∀ b, ρ (j b) = b) → torsionIdeal O (G.A (k + m)) p ≤ kerIdeal j → ∀ q : PrimeSpectrum O, fibreDim (B ⧸ torsionIdeal O B (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := GlobalTheory.T.exists_mulPow_fibreRank_eq_pDivGroup p O G k m
  have hjq : fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim B q :=
    (GlobalTheory.T.linearMapFibreRank_split_comp_surjective O B (G.A (k + m)) (G.A (k + m)) (j : B →ₐ[O] G.A (k + m)).toLinearMap).1 ρ hρ q
  have h1 := fibreDim_eq_ker_mul_range j q
  rw [hjq, G.fibreDim_eq] at h1
  have h2 := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at h2
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega))).trans (by simpa using hj)
  let J : Ideal (G.A k) := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp (r : G.A (k + m) →ₐ[O] G.A k)
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have h5 : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [h5, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from kerIdeal_comp r j,
      Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr, sup_eq_left]
    exact fun a ha => hle ha
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at h2
  have h3 := fibreDim_eq_ker_mul_range (mulBy O B (p ^ m)) q
  have hlin : (j : B →ₐ[O] G.A (k + m)).toLinearMap ∘ₗ (mulBy O B (p ^ m) : B →ₐ[O] B).toLinearMap =
      (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap ∘ₗ ((r.comp j) : B →ₐ[O] G.A k).toLinearMap := by
    ext b
    change j (mulBy O B (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have h4 : fibreRank (mulBy O B (p ^ m) : B →ₐ[O] B).toLinearMap q =
      fibreRank ((r.comp j) : B →ₐ[O] G.A k).toLinearMap q := by
    rw [← (GlobalTheory.T.linearMapFibreRank_split_comp_surjective O B B (G.A (k + m)) _).2.1 _ q hjq, hlin,
      (GlobalTheory.T.linearMapFibreRank_split_comp_surjective O B (G.A k) (G.A (k + m)) _).2.1 _ q (hμq q)]
  change fibreDim (B ⧸ kerIdeal (mulBy O B (p ^ m))) q = _
  rw [h4] at h3
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have h6 : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [← pow_add]; congr 1; ring
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← h6, h1, h3, h2]
  ring

end GlobalTheory.TorsDim
