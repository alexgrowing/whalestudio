import Mathlib

namespace GlobalTheory.FlagZ

def abelExp {ι : Type} {N : ℕ} (lam : ι → Fin N → ℤ) (x : ι × Fin (N + 1)) : ℤ :=
  if h : 0 < (x.2 : ℕ) ∧ (x.2 : ℕ) < N then
    lam x.1 ⟨(x.2 : ℕ) - 1, by omega⟩ - lam x.1 ⟨x.2, h.2⟩
  else 0

theorem abelExp_nonneg {ι : Type} {N : ℕ} (lam : ι → Fin N → ℤ)
    (hlam : ∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a) (x : ι × Fin (N + 1)) : 0 ≤ abelExp lam x := by
  unfold abelExp
  split_ifs with h
  · exact sub_nonneg.2 (hlam _ _ _ (Fin.mk_le_mk.2 (Nat.sub_le _ _)))
  · exact le_rfl

end GlobalTheory.FlagZ
