import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

namespace GlobalTheory.RootEx

theorem exists_finset_eq_sum_indicator_of_periodic {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hcs : IsCompact (tsupport Φ)) (V : AddSubgroup X)
    (hV : IsOpen (V : Set X)) (hper : ∀ x, ∀ y ∈ V, Φ (x + y) = Φ x) :
    ∃ s : Finset X, ∀ t, Φ t = ∑ a ∈ s, Φ a * (V : Set X).indicator (fun _ => (1 : ℂ)) (t - a) := by
  classical
  obtain ⟨s0, -, hcov⟩ := hcs.elim_nhds_subcover (fun a => {x | x - a ∈ V}) (fun a _ =>
    (hV.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [V.zero_mem]))
  refine ⟨(s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, fun t => ?_⟩
  have hmk : ∀ a : X, t - a ∈ V → (a : X ⧸ V) = (t : X ⧸ V) := fun a h => by
    rw [QuotientAddGroup.eq]; simpa [sub_eq_neg_add] using h
  have huniq : ∀ a ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out,
      ∀ b ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, t - a ∈ V → t - b ∈ V → a = b := by
    intro a ha b hb hta htb
    obtain ⟨qa, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨qb, -, rfl⟩ := Finset.mem_image.1 hb
    have h1 := hmk _ hta
    have h2 := hmk _ htb
    rw [QuotientAddGroup.out_eq'] at h1 h2
    rw [h1, h2]
  by_cases h : ∃ a ∈ (s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V))).image Quotient.out, t - a ∈ V
  · obtain ⟨a, ha, hta⟩ := h
    rw [Finset.sum_eq_single a (fun b hb hba => by
      rw [Set.indicator_of_notMem (fun htb => hba (huniq b hb a ha htb hta)), mul_zero])
      (fun h' => absurd ha h'), Set.indicator_of_mem hta, mul_one]
    have := hper a (t - a) hta
    rwa [add_sub_cancel] at this
  · push_neg at h
    rw [Finset.sum_eq_zero (fun b hb => by rw [Set.indicator_of_notMem (h b hb), mul_zero])]
    by_contra hne
    have ht : t ∈ tsupport Φ := subset_tsupport _ hne
    obtain ⟨a0, ha0, hta0⟩ := Set.mem_iUnion₂.1 (hcov ht)
    have hT : (a0 : X ⧸ V) ∈ s0.image (fun a : X => (QuotientAddGroup.mk a : X ⧸ V)) := Finset.mem_image_of_mem _ ha0
    refine h (Quotient.out (a0 : X ⧸ V)) (Finset.mem_image_of_mem _ hT) ?_
    have h1 : ((Quotient.out (a0 : X ⧸ V) : X) : X ⧸ V) = (t : X ⧸ V) := by
      rw [QuotientAddGroup.out_eq']; exact hmk a0 hta0
    rw [QuotientAddGroup.eq] at h1
    simpa [sub_eq_neg_add] using h1

end GlobalTheory.RootEx
