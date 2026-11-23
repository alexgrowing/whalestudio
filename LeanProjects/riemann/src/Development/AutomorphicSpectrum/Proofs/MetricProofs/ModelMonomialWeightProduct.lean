import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeightsStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial

theorem step_monomial : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  classical
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h Φ _ y hy τ i
  obtain ⟨hbase, hstep⟩ := GlobalTheory.T.model_dy_weights Ψ p q Ω n A K₀ J₀ x₀ m h τ i
  have hsplit : ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) =
      (∏ k, y (.inl k)) ^ (rkW i * m (.inl τ) + rkO i * m (.inr τ)) *
        ∏ t, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) := by
    rw [Fintype.prod_sum_type, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hbase k, neg_neg, zpow_natCast]
  have hval : ∀ t : StepIx Ψ p q, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) =
      if (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then (y (.inr t))⁻¹
      else 1 := by
    intro t
    split_ifs with hc
    · rw [(hstep t).1 hc, _root_.zpow_neg, zpow_one]
    · rw [(hstep t).2 hc, neg_zero, zpow_zero]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inl τ, ⟨i, h1⟩⟩ := by
      unfold stepOf
      exact dif_pos h1
    have hW : rkW i = (i : ℕ) + 1 := by unfold rkW; omega
    have hO : rkO i = 0 := by unfold rkO; omega
    rw [hsplit, hW, hO, zero_mul, add_zero, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval,
      if_pos (Or.inl rfl), hso, div_eq_mul_inv]
    intro t ht
    rw [hval, if_neg]
    rintro (h' | ⟨-, -, hp⟩)
    · exact ht h'
    · omega
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩ := by
      unfold stepOf
      exact dif_neg (not_lt.2 h1)
    have hW : rkW i = p := by unfold rkW; omega
    have hO : rkO i = (i : ℕ) - p + 1 := by unfold rkO; omega
    rw [hsplit, hW, hO]
    by_cases hp0 : 0 < p
    · rw [dif_pos hp0]
      have hne : stepOf Ψ p q (τ, i) ≠ ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩ := by
        rw [hso]
        intro he
        exact Sum.inr_ne_inl (congrArg Sigma.fst he)
      rw [Fintype.prod_eq_mul _ _ hne, hval, hval, if_pos (Or.inl rfl),
        if_pos (Or.inr ⟨rfl, show p - 1 + 1 = p by omega, h1⟩), hso]
      · rw [div_eq_mul_inv, mul_inv]
        ring
      · rintro x ⟨hx1, hx2⟩
        rw [hval, if_neg]
        rintro (h' | ⟨hs, hj, -⟩)
        · exact hx1 h'
        · apply hx2
          obtain ⟨s, j⟩ := x
          dsimp only at hs hj
          subst hs
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp; omega)))
    · rw [dif_neg hp0, one_mul, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval, if_pos (Or.inl rfl), hso,
        div_eq_mul_inv]
      intro t ht
      rw [hval, if_neg]
      rintro (h' | ⟨-, hj, -⟩)
      · exact ht h'
      · omega

end GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial
