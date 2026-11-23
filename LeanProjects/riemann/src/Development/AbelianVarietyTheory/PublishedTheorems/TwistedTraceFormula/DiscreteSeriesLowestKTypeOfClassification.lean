import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesLowestKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
      Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) (Formalism.MainNotions.S.lowKSub ε lam σ)) ∧
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)

theorem isKTypeOf_lowKSub_iff {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} :
    IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) ↔ ∃! S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S := by
  constructor
  · intro hT
    refine ⟨lowKSub ε lam σ, hT, fun S hS => ?_⟩
    have hle : S ≤ lowKSub ε lam σ := le_sSup (s := {S | IsKTypeOf ε σ (lowK ε lam) S}) hS
    rcases hT.2.2.1 S hle hS.2.1 with h0 | h1
    · exfalso
      obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      rw [h0] at hv
      exact hv0 ((Submodule.mem_bot ℂ).1 hv)
    · exact h1
  · rintro ⟨S, hS, huniq⟩
    have hset : {S' : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S'} = {S} := by
      ext S'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨huniq S', fun h => h ▸ hS⟩
    have hEq : lowKSub ε lam σ = S := by
      show sSup {S' : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S'} = S
      rw [hset, sSup_singleton]
    rw [hEq]
    exact hS

theorem discreteSeriesLowestKType_iff :
    DiscreteSeriesLowestKType ↔ GlobalTheory.Dec.LowKMultOne ∧ DiscreteSeriesUpqUnique := by
  constructor
  · intro h
    refine ⟨?_, fun n ε lam hp => (h n ε lam hp).2⟩
    intro n ε lam H _ _ σ hp hds S S' hS hS'
    exact (isKTypeOf_lowKSub_iff.1 ((h n ε lam hp).1 H σ hds)).unique hS hS'
  · rintro ⟨hm, hu⟩ n ε lam hp
    refine ⟨fun H _ _ σ hds => ?_, hu n ε lam hp⟩
    obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
    exact isKTypeOf_lowKSub_iff.2 ⟨S, hS, fun S' hS' => hm n ε lam H σ hp hds S' S hS' hS⟩

end GlobalTheory.Published
