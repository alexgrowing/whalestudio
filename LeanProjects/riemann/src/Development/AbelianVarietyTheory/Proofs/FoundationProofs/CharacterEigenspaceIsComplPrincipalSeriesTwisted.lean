import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem Datum.theta_ne_zero_of_mem {G : Type} [Group G] [TopologicalSpace G] {H : Set G} {θ : G → ℂ}
    (hD : Datum H θ) {j : G} (hj : j ∈ H) : θ j ≠ 0 := by
  intro h0
  have h := hD.val_mul j hj j⁻¹ (hD.inv j hj)
  rw [mul_inv_cancel, hD.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem eig_compl_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  intro G V _ _ _ _ _ π hπ H θ hD
  refine ⟨fun u hu he => ?_, fun w => ?_⟩
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ H θ hD u hu
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    have hsum : ∑ j ∈ R, (θ j)⁻¹ • π j u = (R.card : ℂ) • u := by
      rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
      intro j hj
      rw [he j (hRH j hj), smul_smul, inv_mul_cancel₀ (hD.theta_ne_zero_of_mem (hRH j hj)), one_smul]
    rw [hsum] at hs
    exact (smul_eq_zero.mp hs).resolve_left hc
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ H θ hD w
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    refine ⟨(R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w, ?_, ?_⟩
    · intro h hh
      rw [(π h).map_smul, hs h hh]
      exact smul_comm _ _ _
    · have e : w - (R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w
          = (R.card : ℂ)⁻¹ • ∑ j ∈ R, (w - (θ j)⁻¹ • π j w) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      have hθ := hD.theta_ne_zero_of_mem (hRH j hj)
      have e2 : w - (θ j)⁻¹ • π j w = -(θ j)⁻¹ • (π j w - θ j • w) := by
        rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul, neg_sub]
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hRH j hj, w, rfl⟩)

end GlobalTheory.PsType
