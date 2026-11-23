import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

namespace GlobalTheory.FockCompare.WeylInduct

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M]

theorem killed_zero (a : I → Module.End ℂ M) (m : M) : Killed a 0 m ↔ m = 0 := by
  constructor
  · intro h; exact h [] rfl
  · intro h l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact h

theorem killed_succ (a : I → Module.End ℂ M) (N : ℕ) (m : M) :
    Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    obtain rfl | ⟨l', i, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

noncomputable def prodE (E : Module.End ℂ M) (lam : ℂ) : ℕ → ℕ → M → M
  | 0, _, x => x
  | N + 1, j, x => prodE E lam N (j + 1) (E x - ((j : ℂ) * lam) • x)

theorem prodE_comm (E : Module.End ℂ M) (lam : ℂ) (N : ℕ) :
    ∀ (j : ℕ) (x : M), prodE E lam N j (E x) = E (prodE E lam N j x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [← ih, map_sub, map_smul]

theorem shift_prodE (E A : Module.End ℂ M) (lam : ℂ) (h : ∀ x, A (E x) = E (A x) + lam • A x) (N : ℕ) :
    ∀ (j : ℕ) (x : M), A (prodE E lam N (j + 1) x) = prodE E lam N j (A x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [ih, map_sub, map_smul, h]
    congr 1
    push_cast
    module

theorem killed_stable (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (N : ℕ) :
    ∀ (t : ℂ) (x : M), Killed a N x → Killed a N (E x - t • x) := by
  induction N with
  | zero => intro t x hx; rw [killed_zero] at hx ⊢; simp [hx]
  | succ N ih =>
    intro t x hx
    rw [killed_succ] at hx ⊢
    intro i
    have e : a i (E x - t • x) = E (a i x) - (t - lam) • a i x := by
      rw [map_sub, map_smul, h]; module
    rw [e]
    exact ih _ _ (hx i)

theorem prodE_kills (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (h0 : ∀ x, (∀ i, a i x = 0) → E x = 0) (N : ℕ) :
    ∀ x : M, Killed a N x → prodE E lam N 0 x = 0 := by
  induction N with
  | zero => intro x hx; exact (killed_zero a x).1 hx
  | succ N ih =>
    intro x hx
    rw [killed_succ] at hx
    simp only [prodE, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
    rw [prodE_comm]
    refine h0 _ fun i => ?_
    rw [shift_prodE E (a i) lam (h i), ih _ (hx i)]

theorem peel (E : Module.End ℂ M) (lam : ℂ) (hl : lam ≠ 0) (S : M → Prop) (P : Submodule ℂ M)
    (hS : ∀ (t : ℂ) x, S x → S (E x - t • x)) (hE : ∀ x, S x → E x ∈ P) (K : ℕ) :
    ∀ (j : ℕ) (x : M), S x → prodE E lam K (j + 1) x ∈ P → x ∈ P := by
  induction K with
  | zero => intro j x _ hx; exact hx
  | succ K ih =>
    intro j x hx hp
    simp only [prodE] at hp
    have h1 := ih _ _ (hS _ x hx) hp
    have h2 := P.sub_mem (hE x hx) h1
    rw [sub_sub_cancel] at h2
    exact (P.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) hl)).1 h2

theorem mem_of_killed : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  intro I M _ _ a c n e lam hl hc P hv hP N
  set E : Module.End ℂ M := ∑ k, c (e k) * a (e k) with hEdef
  have hEx : ∀ x, E x = ∑ k, c (e k) (a (e k) x) := by
    intro x; simp [hEdef, LinearMap.sum_apply]
  have h : ∀ i x, a i (E x) = E (a i x) + lam • a i x := by
    intro i x
    have := LinearMap.congr_fun (hc i) x
    simpa using this
  have h0 : ∀ x, (∀ i, a i x = 0) → E x = 0 := by
    intro x hx; simp [hEx, hx]
  induction N with
  | zero => intro m hm; rw [(killed_zero a m).1 hm]; exact P.zero_mem
  | succ N ih =>
    intro m hm
    refine peel E lam hl (Killed a (N + 1)) P (killed_stable a E lam h (N + 1)) (fun x hx => ?_) N 0 m hm
      (hv _ fun i => ?_)
    · rw [hEx]
      exact P.sum_mem fun k _ => hP _ _ (ih _ ((killed_succ a N x).1 hx _))
    · rw [shift_prodE E (a i) lam (h i)]
      exact prodE_kills a E lam h h0 N _ ((killed_succ a N m).1 hm i)

end GlobalTheory.FockCompare.WeylInduct

end
