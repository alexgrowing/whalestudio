import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight

noncomputable section

open MeasureTheory Formalism.UG

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cornerU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : L :=
  ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev

def depthU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : ℕ :=
  (-ordL (cornerU k u)).toNat

def shellU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℤ) : Set (cellU y) :=
  {u | Valued.v (cornerU k (u : GU σ n)) ≤ WithZero.exp j}

theorem mem_shellU_iff_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℕ) (u : cellU y) :
    u ∈ shellU k y j ↔ depthU k (u : GU σ n) ≤ j := by
  unfold shellU depthU
  simp only [Set.mem_setOf_eq]
  by_cases h0 : cornerU k (u : GU σ n) = 0
  · rw [h0]; simp [ordL]
  · rw [GlobalTheory.BorelUMod.v_eq_exp h0, WithZero.exp_le_exp]
    omega

theorem mem_shellU_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (u : cellU y) :
    u ∈ shellU k y (depthU k (u : GU σ n)) :=
  (mem_shellU_iff_depth k y _ u).2 le_rfl

theorem shellU_mono {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) {j j' : ℤ} (h : j ≤ j') :
    shellU k y j ⊆ shellU k y j' :=
  fun _ hu => le_trans hu (WithZero.exp_le_exp.2 h)

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
