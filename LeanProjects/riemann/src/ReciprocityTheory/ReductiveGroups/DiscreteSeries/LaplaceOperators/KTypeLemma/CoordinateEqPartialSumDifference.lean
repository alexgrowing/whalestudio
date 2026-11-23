import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem root_cone_functional_natural (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, ℓ (root a b) = N)
    {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, ℓ β = N := by
  classical
  obtain ⟨m, rfl⟩ := hβ
  choose! N hN using hℓ
  refine ⟨∑ a, ∑ b, if a < b then m a b * N a b else 0, ?_⟩
  simp only [map_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [map_smul, hN a b h, smul_eq_mul]
  · simp

def weightPowerSumFunctional (k : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), LinearMap.proj a

theorem k3vdPs_apply (k : ℕ) (μ : Fin n → ℝ) : weightPowerSumFunctional k μ = kirrPs k μ := by
  simp [weightPowerSumFunctional, kirrPs, LinearMap.sum_apply]

theorem partial_sum_of_basis_vector (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp [kirrPs, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter]

theorem partial_sum_of_root (k : ℕ) (a b : Fin n) :
    kirrPs k (root a b) = (if a.val < k then 1 else 0) - (if b.val < k then 1 else 0) := by
  rw [← partial_sum_of_basis_vector, ← partial_sum_of_basis_vector]
  simp [kirrPs, root, Finset.sum_sub_distrib]

theorem root_cone_partial_sum_natural {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : ∃ N : ℕ, kirrPs k β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightPowerSumFunctional k (root a b) = N := by
    intro a b hab
    have hv := Fin.lt_def.1 hab
    rw [k3vdPs_apply, partial_sum_of_root]
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · exact ⟨0, by simp [ha, hb]⟩
    · exact ⟨1, by simp [ha, hb]⟩
    · omega
    · exact ⟨0, by simp [ha, hb]⟩
  obtain ⟨N, hN⟩ := root_cone_functional_natural (weightPowerSumFunctional k) hℓ hβ
  exact ⟨N, by rw [← k3vdPs_apply]; exact hN⟩

def weightHeightFunctional : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) • LinearMap.proj c

theorem k3vdHt_root (a b : Fin n) : weightHeightFunctional (root a b) = ((b : ℕ) : ℝ) - (a : ℕ) := by
  simp only [weightHeightFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    root, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem root_cone_height_natural {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, weightHeightFunctional β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightHeightFunctional (root a b) = N := by
    intro a b hab
    refine ⟨b.val - a.val, ?_⟩
    rw [k3vdHt_root, Nat.cast_sub (le_of_lt (Fin.lt_def.1 hab))]
  exact root_cone_functional_natural weightHeightFunctional hℓ hβ

theorem coordinate_eq_partial_sum_difference (γ : Fin n → ℝ) (a : Fin n) :
    γ a = kirrPs ((a : ℕ) + 1) γ - kirrPs (a : ℕ) γ := by
  unfold kirrPs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    have : c.val ≠ a.val := fun h => hc (Fin.ext h)
    by_cases h1 : c.val < a.val
    · simp [h1, show c.val < a.val + 1 by omega]
    · simp [h1, show ¬ c.val < a.val + 1 by omega]
  · simp

theorem coordinate_difference_le_two (γ : Fin n → ℝ) (hγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0) (a b : Fin n) :
    |γ a - γ b| ≤ 2 := by
  have h1 := coordinate_eq_partial_sum_difference γ a
  have h2 := coordinate_eq_partial_sum_difference γ b
  have a1 := hγ ((a : ℕ) + 1)
  have a0 := hγ (a : ℕ)
  have b1 := hγ ((b : ℕ) + 1)
  have b0 := hγ (b : ℕ)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a0.1, a0.2, b1.1, b1.2, b0.1, b0.2]

theorem strictAnti_of_consecutive_lt {f : Fin n → ℝ} (h : ∀ a b : Fin n, b.val = a.val + 1 → f b < f a) :
    StrictAnti f := by
  intro a b hab
  have key : ∀ d : ℕ, ∀ b : Fin n, b.val = a.val + d + 1 → f b < f a := by
    intro d
    induction d with
    | zero => intro b hb; exact h a b (by omega)
    | succ d ih =>
      intro b hb
      have hc : a.val + d + 1 < n := by have := b.isLt; omega
      exact lt_trans (h ⟨a.val + d + 1, hc⟩ b (by show b.val = a.val + d + 1 + 1; omega))
        (ih ⟨a.val + d + 1, hc⟩ rfl)
  exact key (b.val - a.val - 1) b (by have := Fin.lt_def.1 hab; omega)

theorem rho_consecutive_compact_pair (ε : Fin n → Bool) (a b : Fin n) (hb : b.val = a.val + 1) (he : ε a = ε b) :
    rhoC ε a = rhoC ε b + 1 ∧ rhoN ε a = rhoN ε b := by
  have hab : ∀ c : Fin n, a < c ↔ c = b ∨ b < c := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have hba : ∀ c : Fin n, c < b ↔ c = a ∨ c < a := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      insert b (univ.filter fun c => b < c ∧ ε c = ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr h1, h2⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      insert a (univ.filter fun c => c < a ∧ ε c = ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, he⟩
      · exact ⟨Or.inr h1, h2⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ rfl) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ he) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have nb : b ∉ univ.filter fun c => b < c ∧ ε c = ε b := by simp
  have na : a ∉ univ.filter fun c => c < a ∧ ε c = ε a := by simp
  refine ⟨?_, ?_⟩
  · unfold rhoC
    rw [e1, e2, card_insert_of_notMem nb, card_insert_of_notMem na]
    push_cast
    ring
  · unfold rhoN
    rw [e3, e4]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
