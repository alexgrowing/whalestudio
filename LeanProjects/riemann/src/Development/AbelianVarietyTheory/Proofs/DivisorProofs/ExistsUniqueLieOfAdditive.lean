import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualOfCompatibleModPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualTangentOfCoboundaryOneEqSmulStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.LieOfAdditive

theorem existsUnique_lie_of_additive : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (b : ∀ n, G.A n), (∀ n, ∃ z, cobOne O (G.A n) (b n) = (p : O) ^ n • z) → (∀ n, ∃ z, b (n + 1) = G.mulP n (b n) + (p : O) ^ n • z) → ∃! l : G.dual.Lie, ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ (b n) := by
  intro p O _ _ G b hb hc
  have hu : ∀ n, ∃ u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n},
      ∀ φ : CartierDual O (G.A n), u (dUnit O φ) = Ideal.Quotient.mk _ (φ (b n)) := fun n => by
    obtain ⟨z, hz⟩ := hb n
    exact GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul O (G.A n) ((p : O) ^ n) (b n) z hz
  choose u hu using hu
  let U : ∀ n : ℕ, G.dual.omega →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n} := fun n =>
    (u n).comp ((LinearMap.proj n).comp G.dual.omegaSub.subtype)
  have hU : ∀ n (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n →
      U n w = Ideal.Quotient.mk _ (φ (b n)) := by
    intro n w φ h
    show u n (w.1 n) = _
    rw [← h, hu]
  have key : ∀ n (w : G.dual.omega) (x : O), U (n + 1) w = Ideal.Quotient.mk _ x →
      U n w = Ideal.Quotient.mk _ x := by
    intro n w x hx
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 (n + 1))
    have h1 : dUnit O (CartierDual.map (G.mulP n) φ) = w.1 n := by
      rw [← w.2 n, ← hφ]; exact (cotMap_d _ _).symm
    rw [hU n w _ h1, CartierDual.map_apply]
    rw [hU (n + 1) w φ hφ] at hx
    obtain ⟨z, hz⟩ := hc n
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hx ⊢
    rw [hz, map_add, map_smul, smul_eq_mul] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(p : O) * k - φ z, by linear_combination hk⟩
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.T.existsUnique_dual_of_compatible_mod_pow_of_adicComplete O G.dual.omega (p : O) U key
  refine ⟨l, fun n w φ h => ?_, fun l' hl' => huniq l' fun n w => ?_⟩
  · have := (hl n w).trans (hU n w φ h)
    rwa [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  · obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
    rw [hU n w φ hφ, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hl' n w φ hφ

end GlobalTheory.LieOfAdditive
