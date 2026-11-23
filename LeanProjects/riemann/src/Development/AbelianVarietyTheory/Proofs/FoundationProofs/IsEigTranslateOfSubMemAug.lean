import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwistedStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem isEig_translate_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  intro G V _ _ _ _ _ π hπ J N₀ N₁ θ z hJ hN hsub hconj hdec u u' hu hu' hd
  have hmul : ∀ (a b : G) (v : V), π a (π b v) = π (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  have hw' : IsEig π N₀ (fun _ => 1) (π z u') := by
    intro y hy
    have h1 : z⁻¹ * y * z ∈ N₁ := (hconj _).2 (by
      have : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [this]; exact hy)
    have h2 := hu' _ h1
    have h3 : y * z = z * (z⁻¹ * y * z) := by group
    rw [hmul, h3, ← hmul, h2, map_smul]
  have hmap : ∀ x ∈ aug π N₁ (fun _ => 1), π z x ∈ aug π N₀ (fun _ => 1) := by
    intro x hx
    have : aug π N₁ (fun _ => 1) ≤ (aug π N₀ (fun _ => 1)).comap (π z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hh, w, rfl⟩
      refine Submodule.subset_span ⟨z * h * z⁻¹, (hconj h).1 hh, π z w, ?_⟩
      rw [map_sub, map_smul, hmul, hmul]
      congr 3
      group
    exact this hx
  have hww : π z u - π z u' ∈ aug π N₀ (fun _ => 1) := by
    rw [← map_sub]; exact hmap _ hd
  obtain ⟨R, hR1, hRJ, hS⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ J θ hJ (π z u)
  have hterm : ∀ j ∈ R, (θ j)⁻¹ • π j (π z u) - π z u ∈ aug π N₀ (fun _ => 1) := by
    intro j hj
    have hjJ := hRJ j hj
    obtain ⟨y, hy, h1, h2⟩ := hdec j hjJ
    have hne : θ j ≠ 0 := by
      intro h0
      have := hJ.val_mul j hjJ j⁻¹ (hJ.inv j hjJ)
      rw [mul_inv_cancel, hJ.val_one, h0, zero_mul] at this
      exact one_ne_zero this
    have h3 := hu _ h1
    have h4 : j * z = y * (z * (z⁻¹ * (y⁻¹ * j) * z)) := by group
    have h5 : π j (π z u) = θ j • π y (π z u) := by
      rw [hmul, h4, ← hmul, ← hmul, h3, h2, map_smul, map_smul]
    rw [h5, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact Submodule.subset_span ⟨y, hy, π z u, by rw [one_smul]⟩
  set S : V := ∑ j ∈ R, (θ j)⁻¹ • π j (π z u) with hSdef
  have hc : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, hR1⟩).ne'
  have hA : S - (R.card : ℂ) • π z u ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.sum_mem _ hterm
    rwa [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at this
  have hB : S - (R.card : ℂ) • π z u' ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.add_mem _ hA (Submodule.smul_mem _ (R.card : ℂ) hww)
    rwa [smul_sub, sub_add_sub_cancel] at this
  have hC : IsEig π N₀ (fun _ => 1) (S - (R.card : ℂ) • π z u') := by
    intro y hy
    rw [map_sub, map_smul, hS y (hsub y hy).1, (hsub y hy).2, hw' y hy]
    simp
  have h0 := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ N₀ _ hN).1 _ hB hC
  have hE : π z u' = (R.card : ℂ)⁻¹ • S := by
    rw [sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro j hj
  rw [hE, map_smul, hS j hj, smul_comm]

end GlobalTheory.PsType
