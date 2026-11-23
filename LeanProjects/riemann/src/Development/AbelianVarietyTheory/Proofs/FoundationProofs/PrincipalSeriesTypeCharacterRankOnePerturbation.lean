import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem det_leadingBlock_one_add_vecMulVec_rankOne {k : Type} [Field k] {n : ℕ} (p q : Fin n → k) (a : Fin n) (c : k)
    (hpq : ∀ i, p i * q i = if i = a then c else 0) (m : Fin n) :
    ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m).det = if a ≤ m then 1 + c else 1 := by
  have hM : ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m) =
      1 + Matrix.replicateCol Unit (fun i : {i // i ≤ m} => p i) * Matrix.replicateRow Unit (fun i : {i // i ≤ m} => q i) := by
    ext i j
    simp [Matrix.toSquareBlockProp_def, Matrix.one_apply, Subtype.ext_iff, Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : (fun i : {i // i ≤ m} => q i) ⬝ᵥ (fun i : {i // i ≤ m} => p i) = ∑ i : {i // i ≤ m}, (if (i : Fin n) = a then c else 0) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, hpq]
  rw [hs]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; exact hb (Subtype.ext e)
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro b _
      rw [if_neg]
      intro e; exact h (e ▸ b.2)

theorem rankOne_ev_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) :
    ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem rankOne_ev_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ)
    (u : kˣ) (hu : valuation k (u : k) = 1) : ev χ (u : k) = (χ u : ℂ) := by
  unfold ev
  rw [dif_pos hu]
  simp

theorem rankOne_telescope {G : Type} [CommGroup G] (n : ℕ) (F : ℕ → G) (hF : F n = 1) (a : ℕ) (ha : a < n) :
    ∏ i ∈ Finset.range n, (if a ≤ i then F i / F (i + 1) else 1) = F a := by
  rw [← Finset.prod_filter]
  have hfil : (Finset.range n).filter (fun i => a ≤ i) = Finset.Ico a n := by
    ext i; simp [Finset.mem_Ico, and_comm]
  rw [hfil]
  have h2 : ∀ i, F i / F (i + 1) = (F (i + 1))⁻¹ / (F i)⁻¹ := fun i => by
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [h2]
  rw [Finset.prod_Ico_div (f := fun i => (F i)⁻¹) ha.le, hF]
  simp

theorem theta_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  intro k _ _ _ _ n ψ g p q a u hu hg hpq
  have hmin : ∀ m, minor g m = if a ≤ m then (u : k) else 1 := by
    intro m
    unfold minor
    rw [hg, det_leadingBlock_one_add_vecMulVec_rankOne p q a _ hpq m]
    simp
  let F : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hterm : ∀ m : Fin n, ev (ψ m / nxt ψ m) (minor g m) = ((if a ≤ m then F m / F (m + 1) else 1 : ℂˣ) : ℂ) := by
    intro m
    rw [hmin]
    split_ifs with h
    · rw [rankOne_ev_unit _ _ hu]
      congr 1
      simp only [F, MonoidHom.div_apply, dif_pos m.2]
      congr 1
      unfold nxt
      split_ifs <;> rfl
    · rw [rankOne_ev_one]; simp
  unfold theta
  simp_rw [hterm, Fin.le_iff_val_le_val]
  rw [← Units.coe_prod, Fin.prod_univ_eq_prod_range (fun i => if (a : ℕ) ≤ i then F i / F (i + 1) else 1) n]
  · rw [rankOne_telescope n F (by simp [F]) a a.2]
    simp [F]

end GlobalTheory.PsType
