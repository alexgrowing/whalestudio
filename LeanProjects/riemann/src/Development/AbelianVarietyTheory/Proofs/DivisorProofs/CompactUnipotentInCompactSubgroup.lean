import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LongWConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WhitHered Matrix GlobalTheory.InertSupp

namespace GlobalTheory.UnipCptSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grp_of_le {c : n → ℤ} {g : GL n k} (hg : g ∈ unipOf k c) {m M : ℕ} (hmM : m ≤ M)
    (h : g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)) :
    g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) := by
  have key : ∀ x : GL n k, x ∈ unipOf k c → (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
      ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
    intro x hx hd i j
    by_cases hij : c i < c j
    · refine (hd i j).mono ?_
      have : (m : ℤ) ≤ M := by exact_mod_cast hmM
      nlinarith
    · rw [mem_unipOf.1 hx i j hij]
      by_cases e : i = j
      · subst e
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
  exact ⟨key g hg h.1, key g⁻¹ (inv_mem hg) h.2⟩

theorem isOpen_grp (c : n → ℤ) (m : ℕ) :
    IsOpen (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) := by
  have e : (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) =
      (⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (g.val i j)}) ∩
      ⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) ((g⁻¹).val i j)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem unipB_eq_unipOf (N : ℕ) :
    unipB k (Fin N) = unipOf k (fun i : Fin N => ((i : ℕ) : ℤ)) := by
  ext g
  rw [mem_unipB, mem_unipOf]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    have hji : j ≤ i := by
      rw [not_lt] at hij
      exact Fin.le_def.2 (by exact_mod_cast hij)
    rcases hji.lt_or_eq with h | h
    · rw [h1 i j h, one_apply_ne (ne_of_gt h)]
    · subst h; rw [h2 j, one_apply_eq]
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hji
        omega
      rw [h i j this, one_apply_ne (ne_of_gt hji)]
    · rw [h i i (lt_irrefl _), one_apply_eq]

theorem exists_compact_subgroup_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
      (Q : Set (GL (Fin N) k)), IsCompact Q → Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) →
      ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N Q hQ hQU
  set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  rw [unipB_eq_unipOf] at hQU
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ unipOf k c
      · exact Or.inl (mem_grp_of_le hu hmM hg)
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipOf k c, ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
  · rcases hM hg with h | h
    · exact ⟨h, hQU hg⟩
    · exact absurd (hQU hg) h

end GlobalTheory.UnipCptSub
