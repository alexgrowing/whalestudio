import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf

set_option autoImplicit false

open GlobalTheory.TriFrame

namespace GlobalTheory.TriFrame

theorem matNorm_zero_eq_sup' {C : Type} [NontriviallyNormedField C] {r : ℕ}
    (N : Matrix (Fin (r+1)) (Fin (r+1)) C) :
    matNorm N 0 = Finset.univ.sup' Finset.univ_nonempty (fun l => ‖N l 0‖) := by
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (r+1))) (fun l => ‖N l 0‖)
  have hle : ∀ l, ‖N l 0‖ ≤ ‖N l₀ 0‖ := fun l => by
    rw [← hl₀]
    exact Finset.le_sup' (fun l => ‖N l 0‖) (Finset.mem_univ l)
  rw [hl₀]
  have hsum : ∀ cf : Fin (r+1) → C, (∀ k, (0 : Fin (r+1)) < k → cf k = 0) → ∀ l,
      ∑ j, cf j * N l j = cf 0 * N l 0 := fun cf h l => by
    rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
    intro j _
    rw [h _ (Fin.succ_pos j), zero_mul]
  have hmem : ∀ c : C, c ≠ 0 → ‖c‖ * ‖N l₀ 0‖ ≤ 1 →
      ‖c‖⁻¹ ∈ {t | ∃ cf : Fin (r+1) → C, cf 0 ≠ 0 ∧ (∀ k, 0 < k → cf k = 0) ∧
        (∀ l, ‖∑ j, cf j * N l j‖ ≤ 1) ∧ t = ‖cf 0‖⁻¹} := fun c hc h => by
    have h0 : ∀ k : Fin (r+1), 0 < k → (Pi.single 0 c : Fin (r+1) → C) k = 0 :=
      fun k hk => by simp [hk.ne']
    refine ⟨Pi.single 0 c, by simpa using hc, h0, fun l => ?_, by simp⟩
    rw [hsum _ h0, Pi.single_eq_same, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hle l) (norm_nonneg c)).trans h
  have hlb : ‖N l₀ 0‖ ∈ lowerBounds {t | ∃ cf : Fin (r+1) → C, cf 0 ≠ 0 ∧ (∀ k, 0 < k → cf k = 0) ∧
        (∀ l, ‖∑ j, cf j * N l j‖ ≤ 1) ∧ t = ‖cf 0‖⁻¹} := by
    rintro _ ⟨cf, h₁, h₂, h₃, rfl⟩
    have h := h₃ l₀
    rw [hsum _ h₂, norm_mul] at h
    have hp : 0 < ‖cf 0‖ := norm_pos_iff.2 h₁
    rw [← one_div, le_div_iff₀ hp, mul_comm]
    exact h
  unfold matNorm
  by_cases hz : N l₀ 0 = 0
  · have hm : ∀ c : C, c ≠ 0 → _ := fun c hc => hmem c hc (by simp [hz])
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (le_csInf ⟨_, hm 1 one_ne_zero⟩ hlb)
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm C ε⁻¹
    have hp : 0 < ‖c‖ := (inv_pos.2 hε).trans hc
    refine (csInf_le ⟨_, hlb⟩ (hm c (norm_pos_iff.1 hp))).trans ?_
    rw [hz, norm_zero, zero_add]
    exact (inv_lt_comm₀ hε hp).1 hc |>.le
  · refine IsLeast.csInf_eq ⟨?_, hlb⟩
    have := hmem (N l₀ 0)⁻¹ (inv_ne_zero hz) (by
      rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)])
    rwa [norm_inv, inv_inv] at this

end GlobalTheory.TriFrame
