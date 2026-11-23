import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def shiftTw (τ : H →* H) (d : ℕ) : (Fin (d + 1) → H) →* (Fin (d + 1) → H) where
  toFun g i := if h : i.val < d then g ⟨i.val + 1, Nat.succ_lt_succ h⟩ else τ (g 0)
  map_one' := by
    funext i
    by_cases h : i.val < d <;> simp [h]
  map_mul' g g' := by
    funext i
    by_cases h : i.val < d <;> simp [h]

def prodF {d : ℕ} (g : Fin (d + 1) → H) : H := (List.ofFn g).prod

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

def convF (K : Subgroup H) {d : ℕ} (f : Fin (d + 1) → H → ℂ) : H → ℂ :=
  List.foldr (conv K) (f (Fin.last d)) (List.ofFn fun i : Fin d => f i.castSucc)

end GlobalTheory.LKRes
