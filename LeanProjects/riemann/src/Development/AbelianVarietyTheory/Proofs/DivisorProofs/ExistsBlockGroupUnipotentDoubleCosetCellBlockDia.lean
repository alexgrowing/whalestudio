import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.Cut.Block

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

variable {F : Type} [NormedField F] {m : ℕ}

open Matrix Topology in
variable {F : Type} [NormedField F] {m : ℕ} in
theorem _root_.GlobalTheory.JSW.Cut.Block.mir_inv (a : GL (Fin m) F) (y : Fin m → F) :
    (_root_.GlobalTheory.JSW.KirFin.mir a y)⁻¹ =
      _root_.GlobalTheory.JSW.KirFin.mir a⁻¹ (-((a⁻¹).val *ᵥ y)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [_root_.GlobalTheory.JSW.KirFin.mir_mul]
  simp [mulVec_neg, mulVec_mulVec, ← _root_.GlobalTheory.JSW.KirFin.mir_one]

theorem mir_left_inj {g h : GL (Fin m) F} {x y : Fin m → F} (e : mir g x = mir h y) : g = h := by
  ext i j
  have := congrArg (fun p : GL (Fin (m + 1)) F => p.val i.castSucc j.castSucc) e
  simpa using this

def blocks (U : Subgroup (GL (Fin (m + 1)) F)) : Subgroup (GL (Fin m) F) where
  carrier := {a | ∃ y, mir a y ∈ U}
  one_mem' := ⟨0, by rw [mir_one]; exact U.one_mem⟩
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨a.val *ᵥ z + y, by rw [← mir_mul]; exact U.mul_mem hy hz⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨_, by rw [← mir_inv]; exact U.inv_mem hy⟩

theorem exists_blocks_cell_cor_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  intro F _ m U hUc hUo
  refine ⟨blocks U, isCompact_blocks hUc, ?_, fun b hb => ⟨0, hb⟩, fun h₀ h => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := U.comap cor) (fun b hb => ⟨0, hb⟩) (hUo.preimage continuous_cor)
  constructor
  · rintro ⟨n, hn, u, hu, e⟩
    obtain ⟨n', x, rfl⟩ := exists_mir (lr_of_mem hn)
    have hlu : lr u = lr 1 := by
      have h1 : lr (cor h) = lr (1 * u) := by
        rw [e]
        refine lr_mul_congr ?_ u
        rw [lr_mul_congr (lr_of_mem hn) _, one_mul]
        exact lr_mir h₀ 0
      rw [one_mul] at h1
      rw [← h1]
      exact lr_mir h 0
    obtain ⟨a, y, rfl⟩ := exists_mir hlu
    refine ⟨n', mir_mem_iff.1 hn, a, ⟨y, hu⟩, ?_⟩
    change mir h 0 = mir n' x * mir h₀ 0 * mir a y at e
    rw [mir_mul, mir_mul] at e
    exact mir_left_inj e
  · rintro ⟨n', hn', a, ⟨y, hy⟩, rfl⟩
    refine ⟨mir n' (-((n' * h₀).val *ᵥ y)), mir_mem_iff.2 hn', mir a y, hy, ?_⟩
    change mir (n' * h₀ * a) 0 = mir n' _ * mir h₀ 0 * mir a y
    rw [mir_mul, mir_mul, mulVec_zero, zero_add, add_neg_cancel]

end GlobalTheory.JSW.Cut.Block
