import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_point_count_statement :
    Count := by
  intro Γ _ K₀ H K hKH hHK₀ hK F κ hF hκ ζ
  classical
  have hmul : K.relIndex H * H.relIndex K₀ = K.relIndex K₀ :=
    Subgroup.relIndex_mul_relIndex K H K₀ hKH hHK₀
  have hKH0 : K.relIndex H ≠ 0 := fun h0 => hK (by rw [← hmul, h0, zero_mul])
  have hH0 : H.relIndex K₀ ≠ 0 := fun h0 => hK (by rw [← hmul, h0, mul_zero])
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hH0)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (↥K₀ ⧸ K.subgroupOf K₀) := Nat.finite_of_card_ne_zero hK
  haveI : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero hKH0
  have bound : ∀ ξ : F, Nat.card {x // κ x = ξ} ≤ K.relIndex H := by
    intro ξ
    by_cases hne : Nonempty {x // κ x = ξ}
    · obtain ⟨⟨q0, hq0⟩⟩ := hne
      have memH : ∀ q : {x // κ x = ξ},
          ((q0.out : ↥K₀) : Γ)⁻¹ * ((q.1.out : ↥K₀) : Γ) ∈ H := by
        intro q
        apply hκ
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq', hq0, q.2]
      let f : {x // κ x = ξ} → ↥H ⧸ K.subgroupOf H := fun q => ((⟨_, memH q⟩ : ↥H) : ↥H ⧸ K.subgroupOf H)
      have hinj : Function.Injective f := by
        intro q1 q2 h12
        have h' := QuotientGroup.eq.mp h12
        rw [Subgroup.mem_subgroupOf] at h'
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' q1.1, ← QuotientGroup.out_eq' q2.1]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using h'
      calc Nat.card {x // κ x = ξ} ≤ Nat.card (↥H ⧸ K.subgroupOf H) :=
            Nat.card_le_card_of_injective f hinj
        _ = K.relIndex H := rfl
    · haveI := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hsum : ∑ ξ : F, Nat.card {x // κ x = ξ} = ∑ ξ : F, K.relIndex H := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv κ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hF, mul_comm, hmul]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le (fun ξ _ => bound ξ)).mp hsum ζ (Finset.mem_univ _)
