import Mathlib

namespace GlobalTheory.PowSmulMem

theorem exists_pow_smul_mem {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]
    {O : Subring E} {p : E} (hp : p ∈ O) (hO : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ' : Submodule O V) (hsp : Submodule.span E (Λ' : Set V) = ⊤) (v : V) :
    ∃ a : ℕ, ∀ b, a ≤ b → p ^ b • v ∈ Λ' := by
  have hv : v ∈ Submodule.span E (Λ' : Set V) := hsp ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun b _ => ?_⟩
    exact Λ'.smul_mem (⟨p ^ b, O.pow_mem hp b⟩ : O) hx
  | zero => exact ⟨0, fun b _ => by rw [smul_zero]; exact Λ'.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    refine ⟨max a c, fun b hb => ?_⟩
    rw [smul_add]
    exact Λ'.add_mem (ha b (le_trans (le_max_left _ _) hb)) (hc b (le_trans (le_max_right _ _) hb))
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hO e
    refine ⟨a + c, fun b hb => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have h : p ^ (a + c + d) • e • x = (p ^ c * e) • (p ^ (a + d) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [h]
    exact Λ'.smul_mem (⟨p ^ c * e, hc⟩ : O) (ha _ (Nat.le_add_right _ _))

theorem main : ∀ {E : Type} [inst : CommRing E] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module E V] {O : Subring E} {p : E}, p ∈ O → (∀ (e : E), ∃ (a : ℕ), p ^ a * e ∈ O) → ∀ (Λ Λ' : Submodule (↥O) V), Submodule.FG Λ → Submodule.span E (↑Λ' : Set V) = ⊤ → ∃ (a : ℕ), ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  intro E _ V _ _ O p hp hO Λ Λ' hfg hsp
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose f hf using exists_pow_smul_mem hp hO Λ' hsp
  refine ⟨s.sup f, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hf x _ (Finset.le_sup (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul e x _ hx =>
    have h : p ^ s.sup f • e • x = e • (p ^ s.sup f • x) := by
      change p ^ s.sup f • (e : E) • x = (e : E) • (p ^ s.sup f • x)
      exact smul_comm _ _ _
    rw [h]
    exact Λ'.smul_mem e hx

end GlobalTheory.PowSmulMem
