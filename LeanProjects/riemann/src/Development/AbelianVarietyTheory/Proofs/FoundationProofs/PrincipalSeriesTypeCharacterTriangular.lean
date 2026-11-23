import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem minor_of_triangular (g : GL (Fin n) k) (m : Fin n)
    (h : (∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) :
    minor g m = ∏ i ∈ Finset.univ.filter (fun i => i ≤ m), g.val i i := by
  unfold minor
  have hdet : (g.val.toSquareBlockProp fun i => i ≤ m).det = ∏ i : {i : Fin n // i ≤ m}, g.val i i := by
    rcases h with h | h
    · rw [Matrix.det_of_lowerTriangular]
      · rfl
      · intro i j hij
        exact h i j (OrderDual.toDual_lt_toDual.1 hij)
    · rw [Matrix.det_of_upperTriangular]
      · rfl
      · intro i j hij
        exact h i j hij
  rw [hdet]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => i ≤ m)) (p := fun i => i ≤ m)
    (fun x => by simp) (fun i => g.val i i)).symm

theorem prod_div_nxt (ψ : Fin n → kˣ →* ℂˣ) (a : Fin n) (u : kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m => a ≤ m), (ψ m / nxt ψ m) u = ψ a u := by
  let f : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hf : ∀ m : Fin n, f m = ψ m u := fun m => by
    show (if h : (m : ℕ) < n then ψ ⟨m, h⟩ u else 1) = ψ m u
    rw [dif_pos m.isLt]
  have hnx : ∀ m : Fin n, nxt ψ m u = f (m + 1) := by
    intro m
    unfold nxt
    split_ifs with h
    · simp [f, h]
    · simp [f, h]
  let G : ℕ → ℂˣ := fun j => if (a : ℕ) ≤ j then (f (j + 1))⁻¹ / (f j)⁻¹ else 1
  rw [Finset.prod_filter]
  have hterm : ∀ m : Fin n, (if a ≤ m then (ψ m / nxt ψ m) u else 1) = G m := by
    intro m
    simp only [G, Fin.le_def, MonoidHom.div_apply, hnx, ← hf m, inv_div_inv]
  rw [Finset.prod_congr rfl fun m _ => hterm m, Fin.prod_univ_eq_prod_range G n, ← Finset.prod_filter]
  have hs : (Finset.range n).filter (fun j => (a : ℕ) ≤ j) = Finset.Ico (a : ℕ) n := by
    ext j; simp; omega
  rw [hs, Finset.prod_Ico_div (f := fun j => (f j)⁻¹) a.isLt.le]
  simp [f, hf a]

theorem theta_of_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  intro k _ _ _ _ n ψ g t ht hd htri
  have hmin : ∀ m, minor g m = ((∏ i ∈ Finset.univ.filter (fun i => i ≤ m), t i : kˣ) : k) := by
    intro m
    rw [minor_of_triangular g m htri, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hev : ∀ (χ : kˣ →* ℂˣ) (u : kˣ), valuation k (u : k) = 1 → ev χ u = χ u := by
    intro χ u hu
    unfold ev
    rw [dif_pos hu]
    congr 2
    ext
    rfl
  have hval : ∀ s : Finset (Fin n), valuation k ((∏ i ∈ s, t i : kˣ) : k) = 1 := by
    intro s
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_eq_one fun i _ => ht i
  unfold theta
  rw [Finset.prod_congr rfl fun m _ => by rw [hmin m, hev _ _ (hval _)]]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp only [map_prod]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun m => i ≤ m))
    (by intro x y; simp)]
  exact Finset.prod_congr rfl fun i _ => prod_div_nxt ψ i (t i)

end GlobalTheory.PsType
