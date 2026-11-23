import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

namespace GlobalTheory.NL.Coker

open Formalism.BasicNotions

variable {O : Type} [CommRing O] {n : ℕ} {M : Type} [AddCommGroup M] [Module (LetA O n) M]

def satM (p : ℕ) (P N : Submodule (LetA O n) M) : Submodule (LetA O n) M where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P}
  add_mem' := by
    rintro x y ⟨hx, k, hk1, hk2⟩ ⟨hy, j, hj1, hj2⟩
    refine ⟨N.add_mem hx hy, k + j, ?_, ?_⟩
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk1
      · rw [mul_smul]; exact P.smul_mem _ hj1
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk2
      · rw [mul_smul]; exact P.smul_mem _ hj2
  zero_mem' := ⟨N.zero_mem, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, k, hk1, hk2⟩
    refine ⟨N.smul_mem a hx, k, ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem a hk1
    · rw [smul_comm]; exact P.smul_mem a hk2

theorem satM_le (p : ℕ) (P N : Submodule (LetA O n) M) : satM p P N ≤ N := fun _ hx => hx.1

theorem le_satM (p : ℕ) {P N : Submodule (LetA O n) M} (h : P ≤ N) : P ≤ satM p P N :=
  fun x hx => ⟨h hx, 0, by simpa using hx, by simpa using hx⟩

theorem mem_satM_of_smul {p : ℕ} {P N : Submodule (LetA O n) M} {x : M} (hx : x ∈ N)
    (h1 : ((p : LetA O n)) • x ∈ satM p P N) (h2 : (letπ : LetA O n) • x ∈ satM p P N) :
    x ∈ satM p P N := by
  obtain ⟨-, k, hk1, -⟩ := h1
  obtain ⟨-, j, -, hj2⟩ := h2
  refine ⟨hx, k + j + 1, ?_, ?_⟩
  · have : ((p : LetA O n)) ^ (k + j + 1) • x = ((p : LetA O n)) ^ j • (((p : LetA O n)) ^ k • ((p : LetA O n)) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hk1
  · have : (letπ : LetA O n) ^ (k + j + 1) • x = (letπ : LetA O n) ^ k • ((letπ : LetA O n) ^ j • (letπ : LetA O n) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hj2

theorem uniform {p : ℕ} {P N : Submodule (LetA O n) M} (hN : N.FG) (h : N ≤ satM p P N) :
    ∃ c : ℕ, ∀ z ∈ N, ((p : LetA O n)) ^ c • z ∈ P ∧ (letπ : LetA O n) ^ c • z ∈ P := by
  classical
  obtain ⟨G, rfl⟩ := hN
  have hk : ∀ x ∈ G, ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P :=
    fun x hx => (h (Submodule.subset_span hx)).2
  choose! k hk using hk
  refine ⟨G.sup k, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    have hle : k x ≤ G.sup k := Finset.le_sup hx
    obtain ⟨h1, h2⟩ := hk x hx
    constructor
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h1
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h2
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by rw [smul_add]; exact P.add_mem hx.1 hy.1, by rw [smul_add]; exact P.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨by rw [smul_comm]; exact P.smul_mem a hx.1, by rw [smul_comm]; exact P.smul_mem a hx.2⟩

end GlobalTheory.NL.Coker
