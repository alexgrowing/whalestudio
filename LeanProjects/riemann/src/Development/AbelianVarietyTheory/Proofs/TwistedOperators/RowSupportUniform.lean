import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport

theorem exists_box {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : Set (n → k)) (hW : W ∈ 𝓝 (0 : n → k)) :
    ∃ B : Set (n → k), IsCompact B ∧ ∀ u, u ∉ B → ∃ β ∈ W, ψ (u ⬝ᵥ β) ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (AddChar.map_zero_eq_one ψ)
  have hU : ∀ s : n, {x : k | (Pi.single s x : n → k) ∈ W} ∈ 𝓝 (0 : k) := by
    intro s
    have hcont : Continuous fun x : k => (Pi.single s x : n → k) := by
      refine continuous_pi fun j => ?_
      simp only [Pi.single_apply]
      split_ifs
      · exact continuous_id
      · exact continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp (Filter.iInter_mem.mpr hU)
  refine ⟨Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k a / (γ : ValueGroupWithZero k)},
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩
  intro u hu
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, not_forall, not_le] at hu
  obtain ⟨s, hs⟩ := hu
  have hus : u s ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    exact not_lt.mpr zero_le hs
  have hv : 0 < valuation k (u s) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hus
  refine ⟨Pi.single s (a / u s), ?_, ?_⟩
  · have hsmall : valuation k (a / u s) < γ := by
      rw [map_div₀, div_lt_iff₀ hv]
      have hg : (0 : ValueGroupWithZero k) < γ := by
        rw [zero_lt_iff]
        exact γ.ne_zero
      rw [div_lt_iff₀ hg] at hs
      simpa [mul_comm] using hs
    exact Set.mem_iInter.mp (hγ hsmall) s
  · rw [dotProduct_single, mul_div_cancel₀ _ hus]
    exact ha

theorem row_support_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : ψ ≠ 1) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (F : A) (Ω : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact Ω), ∃ B : Set (n → k), IsCompact B ∧ ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∀ w ∈ Ω, ∀ u, u ∉ B → l (σ (rowE c p u) (σ w F)) = 0 := by
  intro k _ _ _ _ n _ _ c p hp hc ψ hψ A _ _ σ hσ F Ω hΩ
  set S : Set (GL (n ⊕ Fin c) k) := {g | σ g F = F} with hSdef
  have hS : IsOpen S := hσ F
  have hcol : Continuous fun β : n → k => colE (k := k) c (p + 1) β :=
    ExchangeSupport.continuous_colE
  have hfix : ∀ᶠ β in 𝓝 (0 : n → k), ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F := by
    refine hΩ.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc2 : Continuous fun z : (n → k) × GL (n ⊕ Fin c) k => z.2⁻¹ * colE c (p + 1) z.1 * z.2 :=
      ((continuous_snd.inv).mul (hcol.comp continuous_fst)).mul continuous_snd
    have hmem : ((0 : n → k), w).2⁻¹ * colE c (p + 1) ((0 : n → k), w).1 * ((0 : n → k), w).2 ∈ S := by
      simp [hSdef, ExchangeSupport.colE_zero]
    filter_upwards [hc2.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with z hz
    have hz' : σ (z.2⁻¹ * colE c (p + 1) z.1 * z.2) F = F := hz
    calc σ (colE c (p + 1) z.1) (σ z.2 F)
        = σ (z.2 * (z.2⁻¹ * colE c (p + 1) z.1 * z.2)) F := by
          rw [map_mul σ z.2, Module.End.mul_apply, map_mul, map_mul, Module.End.mul_apply,
            Module.End.mul_apply]
          rw [← Module.End.mul_apply (σ z.2), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ z.2 F := by rw [map_mul, Module.End.mul_apply, hz']
  obtain ⟨B, hB, hBout⟩ := exists_box hψ {β | ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F} hfix
  refine ⟨B, hB, fun l hl w hw u hu => ?_⟩
  obtain ⟨β, hβ, hne⟩ := hBout u hu
  obtain ⟨hN, hsum⟩ := ExchangeSupport.conj_col (k := k) (n := n) hp hc u β
  have key := hl _ hN (σ (rowE c p u) (σ w F))
  rw [hsum] at key
  have lhs : σ (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) (σ (rowE c p u) (σ w F)) =
      σ (rowE c p u) (σ w F) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hβ w hw]
  rw [lhs] at key
  have hne' : (ψ (u ⬝ᵥ β) : ℂ) ≠ 1 := by
    intro h
    exact hne (Subtype.ext (by simpa using h))
  have : (1 - (ψ (u ⬝ᵥ β) : ℂ)) * l (σ (rowE c p u) (σ w F)) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne'
  · exact h

end GlobalTheory.RootEx.RowSupport
