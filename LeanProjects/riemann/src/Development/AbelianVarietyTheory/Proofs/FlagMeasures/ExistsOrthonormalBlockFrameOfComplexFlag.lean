import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

open scoped InnerProductSpace

theorem mem_of_orth_piece {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : Submodule ℂ E} (hAB : A ≤ B) {y : E} (hy : y ∈ B)
    (ho : y ∈ (Aᗮ ⊓ B)ᗮ) : y ∈ A := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := A) y
  have hwB : w ∈ B := by
    have := B.sub_mem hy (hAB hv)
    simpa using this
  have h1 : ⟪w, v + w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 ho w ⟨hw, hwB⟩
  have h2 : ⟪w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hw v hv
  rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
  simpa [h1] using hv

theorem exists_orthonormal_family {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Submodule ℂ E) {r : ℕ} (hr : Module.finrank ℂ P = r) :
    ∃ e : Fin r → E, Orthonormal ℂ e ∧ (∀ j, e j ∈ P) ∧
      ∀ y, (∀ j, ⟪e j, y⟫_ℂ = 0) → y ∈ Pᗮ := by
  subst hr
  let b := stdOrthonormalBasis ℂ P
  refine ⟨fun j => (b j : E), ?_, fun j => (b j).2, fun y hy => ?_⟩
  · exact b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have h := congrArg (fun x : P => (x : E)) (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, hy j, mul_zero]

theorem exists_orthonormal_block_frame :
    ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ →
      (∀ b, m ≤ b → W b = ⊤) →
      (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) →
      ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧
        ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  intro n m W r hmono h0 htop hr
  let L : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin n)) := fun b => (W b).map L.toLinearMap
  have hV : ∀ b y, L y ∈ V b ↔ y ∈ W b := fun b y => by
    simp [V]
  have hVm : Monotone V := fun a b h => Submodule.map_mono (hmono h)
  have hfin : ∀ b, Module.finrank ℂ ((V b)ᗮ ⊓ V (b + 1) : Submodule ℂ _) = r b := fun b => by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Nat.le_succ b))
    have h2 : ∀ c, Module.finrank ℂ (V c) = Module.finrank ℂ (W c) := fun c =>
      LinearEquiv.finrank_map_eq L (W c)
    rw [h2, h2, hr] at h1
    exact Nat.add_left_cancel h1
  choose e he hmem hdet using fun b => exists_orthonormal_family _ (hfin b)
  let U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ := fun b => Matrix.of fun i j => e b j i
  have hU : ∀ b y j, ((U b)ᴴ *ᵥ y) j = ⟪e b j, L y⟫_ℂ := fun b y j => by
    simp [U, L, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hUU : ∀ b b' j j', ((U b)ᴴ * U b') j j' = ⟪e b j, e b' j'⟫_ℂ := fun b b' j j' => by
    simp [U, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hflag : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
    intro k y
    constructor
    · intro hy b hb
      funext j
      rw [hU]
      exact (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm hb ((hV k y).2 hy))
    · intro hy
      have key : ∀ d, L y ∈ V (k + d) → L y ∈ V k := by
        intro d
        induction d with
        | zero => exact id
        | succ d ih =>
          intro h
          refine ih (mem_of_orth_piece (hVm (Nat.le_succ (k + d))) h (hdet _ _ fun j => ?_))
          rw [← hU, hy _ (Nat.le_add_right k d)]
          rfl
      refine (hV k y).1 (key m ((hV _ y).2 ?_))
      rw [htop _ (Nat.le_add_left m k)]
      trivial
  have h1 : ∀ b, (U b)ᴴ * U b = 1 := fun b => by
    ext j j'
    rw [hUU, orthonormal_iff_ite.1 (he b), Matrix.one_apply]
  have hlt : ∀ b b', b' < b → ∀ j j', ⟪e b j, e b' j'⟫_ℂ = 0 := fun b b' h j j' =>
    (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm (Nat.succ_le_of_lt h) (hmem b' j').2)
  have h2 : ∀ b b', b ≠ b' → (U b)ᴴ * U b' = 0 := fun b b' h => by
    ext j j'
    rw [hUU, Matrix.zero_apply]
    rcases lt_or_gt_of_ne h with h | h
    · rw [inner_eq_zero_symm]; exact hlt _ _ h _ _
    · exact hlt _ _ h _ _
  refine ⟨U, ⟨h1, h2, ?_⟩, hflag⟩
  have h3 : ∀ y, (1 - ∑ b ∈ Finset.range m, U b * (U b)ᴴ) *ᵥ y = 0 := by
    intro y
    rw [← Submodule.mem_bot ℂ, ← h0, hflag]
    intro b _
    by_cases hb : m ≤ b
    · refine (hflag m _).1 ?_ b hb
      rw [htop m le_rfl]; trivial
    · rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_sum,
        Finset.sum_eq_single b, ← Matrix.mul_assoc, h1]
      · simp
      · intro c _ hc
        rw [← Matrix.mul_assoc, h2 _ _ hc.symm, Matrix.zero_mul]
      · intro hc
        exact absurd (Finset.mem_range.2 (by omega)) hc
  refine (sub_eq_zero.1 ?_).symm
  ext i k
  have := congrFun (h3 (Pi.single k 1)) i
  simpa using this

end GlobalTheory.RadCov
