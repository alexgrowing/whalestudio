import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmoduleStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.WDer

theorem X_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (j : τ) : (X j : MvPowerSeries τ (Fr p k)) ∈ intBy p k τ 1 := by
  classical
  intro β
  refine ⟨if β = Finsupp.single j 1 then 1 else 0, ?_⟩
  rw [coeff_X, one_mul]
  split_ifs <;> simp

theorem lift_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (f : MvPowerSeries τ k) : lift p f ∈ intBy p k τ 1 := by
  intro β
  exact ⟨WittVector.teichmuller p (coeff β f), by rw [coeff_lift, one_mul]⟩

theorem coboundaryOne_teichmullerLift_mem_integralDifferential (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
    (g : MvPowerSeries (Fin d) (Fr p k)) (hg : g ∈ quasiInt p k (Fin d)) :
    cob1 (fun i => lift p (μ i)) g ∈ quasiInt p k (Fin d ⊕ Fin d) := by
  unfold cob1 inL inR
  refine sub_mem (sub_mem ?_ ?_) ?_
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_lift p (hμ.const i)) (fun i => lift_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  intro p _ k _ _ _ d μ hμ N g h hN hg hh hcob α i hα
  classical
  by_cases hi : α i = 0
  · exact ⟨0, by simp [hi]⟩
  set β : Fin d →₀ ℕ := α - Finsupp.single i 1 with hβdef
  have hαβ : α = β + Finsupp.single i 1 := by
    ext j
    simp only [hβdef, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with hj
    · subst hj; omega
    · omega
  have hβdeg : β.degree + 1 = N := by
    rw [← hα, hαβ, map_add, Finsupp.degree_single]
  have hβ0 : β ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hβdeg
    omega
  set γ : Fin d ⊕ Fin d →₀ ℕ := β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 with hγdef
  have hγdeg : γ.degree = N := by
    rw [hγdef, map_add, Finsupp.degree_mapDomain, Finsupp.degree_single, hβdeg]
  have hγi : γ (Sum.inr i) = 1 := by
    rw [hγdef, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, Finsupp.single_eq_same, zero_add]
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

  obtain ⟨wg, hwg⟩ := coboundaryOne_teichmullerLift_mem_integralDifferential p k d μ hμ g hg γ (Sum.inr i)
  rw [hγi, Nat.cast_one, one_mul] at hwg
  obtain ⟨wt, hwt⟩ := hcob γ hγdeg

  have hlin : ∀ j (a : Fin d ⊕ Fin d →₀ ℕ), a.degree ≤ 1 →
      coeff a (lift p (μ j)) = coeff a (addLaw (Fr p k) d j) :=
    fun j a ha => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ j a ha).2
  have hlead := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun j => lift p (μ j)) N hlin).1 h hh γ).2
    hγdeg.le
  have hhom := (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).2.2.2 h β i hβ0
  rw [formalCoboundary_add (fun j => constantCoeff_lift p (hμ.const j)), map_add, hwg, hlead,
    hhom, ← hαβ] at hwt
  refine ⟨wt - wg, ?_⟩
  have hai : α i = β i + 1 := by
    conv_lhs => rw [hαβ]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [map_sub, ← hwt, hai, add_sub_cancel_left]

end GlobalTheory.Katz.WDer
