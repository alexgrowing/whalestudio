import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTauStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariantStatement

open GlobalTheory.K5

namespace GlobalTheory.K5.KernLoc

theorem kern_of (SPAN : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) (ORTH : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j)) : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt p w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong p k (τ w - w) o → Cong p k o 0 := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq k N w o hw hwH ho hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hζalg : IsAlgZp p (T.ζ N) := by
    refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos N) 1, ?_⟩
    simp [(T.prim N).pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g (T.ζ N) = T.ζ N := fun g hg => hg (T.ζ N) hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) (T.qq N) = T.ζ N ^ i * T.qq N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, hfixζ _ (Subgroup.pow_mem _ hτ i)]
      ring
  have hτi : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i

  have hτN : (τ ^ (p ^ N)) w = w := by
    apply hwH
    refine ⟨hτi _, ?_⟩
    show (τ ^ (p ^ N)) (T.qq N) = T.qq N
    rw [hτpow, (T.prim N).pow_eq_one, one_mul]

  obtain ⟨z, hz, hze⟩ := hc
  have hzH : ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z := by
    intro g hg
    have hg1 : g ∈ Ggeo p Ω := hg.1
    have hg2 : g (T.qq N) = T.qq N := hg.2
    have hconj : τ⁻¹ * g * τ ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) := by
      refine ⟨(Ggeo p Ω).mul_mem ((Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem hτ) hg1) hτ, ?_⟩
      show (τ⁻¹ * g * τ) (T.qq N) = T.qq N
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq, map_mul, hfixζ g hg1, hg2, ← hτq,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hgτw : g (τ w) = τ w := by
      have := hwH _ hconj
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      have h2 := congrArg τ this
      rwa [← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
    have e := congrArg g hze
    rw [map_sub, map_sub, hgτw, hwH g hg, ho g hg1, map_mul, map_pow, map_natCast, hze] at e
    exact (mul_left_cancel₀ (pow_ne_zero k hp0) e).symm
  obtain ⟨c, hcfix, hzc⟩ := SPAN p Ω hΩ T τ hτ hτq N z hzH

  have hsumz : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) z = (p : Ω) ^ N * c 0 := by
    have h1 : ∀ i j : ℕ, (τ ^ i) (c j * T.qq N ^ j) = c j * T.qq N ^ j * (T.ζ N ^ j) ^ i := by
      intro i j
      rw [map_mul, map_pow, hcfix j _ (hτi i), hτpow]
      ring
    rw [hzc]
    simp_rw [map_sum, h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro j hj hj0
      have hj' := Finset.mem_range.1 hj
      have hne : T.ζ N ^ j ≠ 1 := (T.prim N).pow_ne_one_of_pos_of_lt hj0 hj'
      rw [geom_sum_eq hne, ← pow_mul, mul_comm j, pow_mul, (T.prim N).pow_eq_one, one_pow, sub_self,
        zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (pow_pos (Fact.out : p.Prime).pos N)) h
  have hsumL : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) (τ w - w - o) = -((p : Ω) ^ N * o) := by
    have h1 : ∀ i : ℕ, (τ ^ i) (τ w - w - o) = (τ ^ (i + 1)) w - (τ ^ i) w - o := by
      intro i
      rw [map_sub, map_sub, pow_succ, AlgEquiv.mul_apply, ho _ (hτi i)]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (τ ^ i) w), hτN, pow_zero,
      AlgEquiv.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have key : -((p : Ω) ^ N * o) = (p : Ω) ^ k * ((p : Ω) ^ N * c 0) := by
    rw [← hsumL, ← hsumz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hze, map_mul, map_pow, map_natCast]
  have hc0 : IsInt p (c 0) := ORTH p Ω hΩ T N c hcfix (hzc ▸ hz) 0 (pow_pos (Fact.out : p.Prime).pos N)
  refine ⟨-c 0, hc0.neg, ?_⟩
  have hpN : (p : Ω) ^ N ≠ 0 := pow_ne_zero N hp0
  apply mul_left_cancel₀ hpN
  linear_combination -key

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt p w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong p k (τ w - w) o → Cong p k o 0 :=
  kern_of GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion

end GlobalTheory.K5.KernLoc
