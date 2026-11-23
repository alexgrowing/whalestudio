import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvUnifA
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.AutomorphicForms.Cartan
import GroundTheory.AutomorphicForms.IwahoriFactorization

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic GroundTheory.Automorphic.Cartan
  GroundTheory.Automorphic.Parabolic ValuativeRel Matrix

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem diagPow_add (μ ν : Fin n → ℤ) : diagPow F n (μ + ν) = diagPow F n μ * diagPow F n ν := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F)]

theorem diagPow_zero : diagPow F n 0 = 1 := by
  refine Units.ext ?_
  rw [coe_diagPow, Units.val_one]
  simp

theorem diagPow_neg (μ : Fin n → ℤ) : diagPow F n (-μ) = (diagPow F n μ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diagPow_add, neg_add_cancel, diagPow_zero]

theorem diagPow_conj_apply (c : Fin n → ℤ) (x : GL (Fin n) F) (i j : Fin n) :
    ((diagPow F n c * x * (diagPow F n c)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ c i * x i j * (GLnLocal.uniformizer F : F) ^ (-c j) := by
  rw [Units.val_mul, Units.val_mul, coe_diagPow]
  change (diagonal (fun i => (GLnLocal.uniformizer F : F) ^ c i) * (x : Matrix (Fin n) (Fin n) F) *
    diagonal fun i => (GLnLocal.uniformizer F : F) ^ (-c i)) i j = _
  rw [mul_diagonal, diagonal_mul]

theorem conj_mem_congruenceSubgroup_of_zero {r : ℕ} (c : Fin n → ℤ) (H : Subgroup (GL (Fin n) F))
    (hH : H ≤ GLnLocal.congruenceSubgroup F n r) (hz : ∀ x ∈ H, ∀ i j, c i < c j → x i j = 0)
    {x : GL (Fin n) F} (hx : x ∈ H) :
    diagPow F n c * x * (diagPow F n c)⁻¹ ∈ GLnLocal.congruenceSubgroup F n r := by
  have hb : ∀ y ∈ H, ∀ i j, valuation F
      (((diagPow F n c * y * (diagPow F n c)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ r := by
    intro y hy i j
    have hyK := ((GLnLocal.mem_congruenceSubgroup_iff F n).1 (hH hy)).2 i j
    rw [diagPow_conj_apply]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm ((GLnLocal.uniformizer F : F) ^ c i), mul_assoc,
        ← zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F), add_neg_cancel, zpow_zero,
        mul_one]
      exact hyK
    · rw [one_apply_ne hij, sub_zero] at hyK ⊢
      by_cases hlt : c i < c j
      · rw [hz y hy i j hlt, mul_zero, zero_mul, map_zero]
        exact zero_le
      · rw [not_lt] at hlt
        obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hlt)
        have he : (GLnLocal.uniformizer F : F) ^ c i * y i j * (GLnLocal.uniformizer F : F) ^ (-c j) =
            (GLnLocal.uniformizer F : F) ^ d * y i j := by
          rw [mul_comm _ (y i j), mul_assoc,
            ← zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F), ← sub_eq_add_neg, hd,
            zpow_natCast, mul_comm]
        rw [he, map_mul, map_pow]
        calc valuation F (GLnLocal.uniformizer F : F) ^ d * valuation F (y i j)
            ≤ 1 * valuation F (y i j) := by
              gcongr
              exact pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le d
          _ = valuation F (y i j) := one_mul _
          _ ≤ _ := hyK
  apply mem_congruenceSubgroup_of_le
  · exact hb x hx
  · have he : (diagPow F n c * x * (diagPow F n c)⁻¹)⁻¹ = diagPow F n c * x⁻¹ * (diagPow F n c)⁻¹ := by
      group
    rw [he]
    exact hb x⁻¹ (H.inv_mem hx)

theorem diagPow_comm_of_mem_levi (c : Fin n → ℤ) {y : GL (Fin n) F}
    (hy : y ∈ levi F n (id : Fin n → Fin n)) : diagPow F n c * y = y * diagPow F n c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagPow]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i = j
  · subst hij
    rw [mul_comm]
  · have h0 := mem_levi.1 hy i j hij
    simp only [h0, mul_zero, zero_mul]

theorem dominant_conj {r : ℕ} (hr : 1 ≤ r) {μ ν : Fin n → ℤ} (hμ : IsDominant μ)
    (hν : IsDominant ν) {κ : GL (Fin n) F} (hκ : κ ∈ GLnLocal.congruenceSubgroup F n r) :
    ∃ a ∈ GLnLocal.congruenceSubgroup F n r, ∃ b ∈ GLnLocal.congruenceSubgroup F n r,
      ∃ c ∈ GLnLocal.congruenceSubgroup F n r,
        diagPow F n μ * κ * diagPow F n ν = a * (diagPow F n μ * diagPow F n ν) * b * c := by
  obtain ⟨z, hz, y, hy, x, hx, hk⟩ := congruenceSubgroup_iwahoriFactorization (F := F)
    (id : Fin n → Fin n) hr κ⁻¹ (inv_mem hκ)
  have hκ' : κ = x⁻¹ * y⁻¹ * z⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, ← hk, inv_inv]
  refine ⟨diagPow F n μ * x⁻¹ * (diagPow F n μ)⁻¹, ?_, y⁻¹, inv_mem hy.1,
    diagPow F n (-ν) * z⁻¹ * (diagPow F n (-ν))⁻¹, ?_, ?_⟩
  · refine conj_mem_congruenceSubgroup_of_zero μ
      (GLnLocal.congruenceSubgroup F n r ⊓ unipotentRadical F n (id : Fin n → Fin n)) inf_le_left ?_
      (inv_mem hx)
    intro w hw i j hij
    have hji : j < i := by
      by_contra h
      rw [not_lt] at h
      exact absurd hij (not_lt.2 (hμ h))
    exact (Iwasawa.mem_blockUpper F n).1 (mem_unipotentRadical.1 hw.2).1 hji
  · refine conj_mem_congruenceSubgroup_of_zero (-ν)
      (GLnLocal.congruenceSubgroup F n r ⊓ oppositeUnipotentRadical F n (id : Fin n → Fin n)) inf_le_left ?_
      (inv_mem hz)
    intro w hw i j hij
    have hij' : i < j := by
      by_contra h
      rw [not_lt] at h
      have := hν h
      simp only [Pi.neg_apply] at hij
      omega
    exact (mem_oppositeUnipotentRadical.1 hw.2).1 i j hij'
  · have hc : diagPow F n ν * y⁻¹ = y⁻¹ * diagPow F n ν :=
      diagPow_comm_of_mem_levi ν (inv_mem hy.2)
    have hb : y⁻¹ = diagPow F n ν * y⁻¹ * (diagPow F n ν)⁻¹ := by
      rw [hc, mul_inv_cancel_right]
    rw [diagPow_neg, hκ']
    conv_lhs => rw [hb]
    group

end Local

def gen (n : ℕ) (i : Fin (n + 1)) (j : Fin n) : ℤ :=
  if (i : ℕ) = n then -1 else if (j : ℕ) ≤ i then 1 else 0

theorem gen_dominant (n : ℕ) (i : Fin (n + 1)) : IsDominant (gen n i) := by
  intro j j' hjj'
  have h : (j : ℕ) ≤ j' := hjj'
  simp only [gen]
  split_ifs <;> omega

theorem dom_nonneg {n : ℕ} (P : (Fin n → ℤ) → Prop) (h0 : P 0) (hgen : ∀ i, P (gen n i))
    (hadd : ∀ μ ν, IsDominant μ → IsDominant ν → P μ → P ν → P (μ + ν)) :
    ∀ N : ℕ, ∀ μ : Fin n → ℤ, IsDominant μ → (∀ j, 0 ≤ μ j) → ∑ j, μ j ≤ N → P μ := by
  classical
  intro N
  induction N with
  | zero =>
    intro μ _ hμ0 hs
    have hs0 : ∑ j, μ j = 0 :=
      le_antisymm (by exact_mod_cast hs) (Finset.sum_nonneg fun j _ => hμ0 j)
    have : μ = 0 := funext fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hμ0 j)).1 hs0 j (Finset.mem_univ j)
    rw [this]; exact h0
  | succ N ih =>
    intro μ hμ hμ0 hs
    by_cases hall : ∀ j, μ j = 0
    · have : μ = 0 := funext hall
      rw [this]; exact h0
    obtain ⟨j0, hj0⟩ := not_forall.1 hall
    obtain ⟨i, hi_pos, hi_max⟩ : ∃ i : Fin n, 0 < μ i ∧ ∀ j, 0 < μ j → j ≤ i := by
      have hSne : (Finset.univ.filter fun j => 0 < μ j).Nonempty :=
        ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (hμ0 j0) (Ne.symm hj0)⟩⟩
      exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
        fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
    have hle : ∀ j : Fin n, (j : ℕ) ≤ i → 1 ≤ μ j := fun j hj => by
      have := hμ (show j ≤ i from hj); omega
    have hgt : ∀ j : Fin n, ¬ (j : ℕ) ≤ i → μ j = 0 := fun j hj => by
      have h1 := hμ0 j
      by_contra hne
      exact hj (hi_max j (lt_of_le_of_ne h1 (Ne.symm hne)))
    have hin : ¬ ((i : ℕ) = n) := by have := i.2; omega
    have hν1 : ∀ j : Fin n, (j : ℕ) ≤ i → gen n (Fin.castSucc i) j = 1 := fun j hj => by
      simp only [gen, Fin.val_castSucc, if_neg hin, if_pos hj]
    have hν0 : ∀ j : Fin n, ¬ (j : ℕ) ≤ i → gen n (Fin.castSucc i) j = 0 := fun j hj => by
      simp only [gen, Fin.val_castSucc, if_neg hin, if_neg hj]
    have hdom' : IsDominant (μ - gen n (Fin.castSucc i)) := by
      intro j j' hjj'
      have h := hμ hjj'
      have hj : (j : ℕ) ≤ j' := hjj'
      simp only [Pi.sub_apply]
      by_cases h1 : (j' : ℕ) ≤ i
      · rw [hν1 j' h1, hν1 j (le_trans hj h1)]; omega
      · rw [hν0 j' h1, hgt j' h1]
        by_cases h2 : (j : ℕ) ≤ i
        · rw [hν1 j h2]; have := hle j h2; omega
        · rw [hν0 j h2]; have := hμ0 j; omega
    have hdec : μ = gen n (Fin.castSucc i) + (μ - gen n (Fin.castSucc i)) := by abel
    rw [hdec]
    refine hadd _ _ (gen_dominant n _) hdom' (hgen _) (ih _ hdom' ?_ ?_)
    · intro j
      simp only [Pi.sub_apply]
      by_cases h2 : (j : ℕ) ≤ i
      · rw [hν1 j h2]; have := hle j h2; omega
      · rw [hν0 j h2]; have := hμ0 j; omega
    · have hνsum : 1 ≤ ∑ j, gen n (Fin.castSucc i) j := by
        calc (1 : ℤ) = gen n (Fin.castSucc i) i := (hν1 i le_rfl).symm
          _ ≤ ∑ j, gen n (Fin.castSucc i) j := Finset.single_le_sum (fun j _ => by
              by_cases h2 : (j : ℕ) ≤ i
              · rw [hν1 j h2]; norm_num
              · rw [hν0 j h2]) (Finset.mem_univ i)
      have hsub : ∑ j, (μ - gen n (Fin.castSucc i)) j =
          ∑ j, μ j - ∑ j, gen n (Fin.castSucc i) j := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [hsub]
      push_cast at hs ⊢
      omega

theorem dom_induct {n : ℕ} (P : (Fin n → ℤ) → Prop) (h0 : P 0) (hgen : ∀ i, P (gen n i))
    (hadd : ∀ μ ν, IsDominant μ → IsDominant ν → P μ → P ν → P (μ + ν)) :
    ∀ μ, IsDominant μ → P μ := by
  have hnn := dom_nonneg P h0 hgen hadd
  have hneg : ∀ k : ℕ, P (fun _ => -(k : ℤ)) := by
    intro k
    induction k with
    | zero =>
      have : (fun _ : Fin n => -((0 : ℕ) : ℤ)) = 0 := by funext; simp
      rw [this]; exact h0
    | succ k ih =>
      have hl : gen n (Fin.last n) = fun _ => -1 := by funext j; simp [gen]
      have : (fun _ : Fin n => -((k + 1 : ℕ) : ℤ)) = (fun _ => -(k : ℤ)) + gen n (Fin.last n) := by
        rw [hl]; funext j; simp only [Pi.add_apply]; push_cast; ring
      rw [this]
      exact hadd _ _ (fun _ _ _ => le_rfl) (gen_dominant n _) ih (hgen _)
  intro μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∑ j, (μ j).natAbs := ⟨_, rfl⟩
  have hbound : ∀ j, -(d : ℤ) ≤ μ j := by
    intro j
    have h1 : (μ j).natAbs ≤ d := by
      rw [hd]
      exact Finset.single_le_sum (f := fun j => (μ j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h1' : ((μ j).natAbs : ℤ) ≤ d := by exact_mod_cast h1
    have h2 := neg_abs_le (μ j)
    rw [← Int.natCast_natAbs] at h2
    omega
  have hdec : μ = (μ + fun _ => (d : ℤ)) + fun _ => -(d : ℤ) := by
    funext j; simp only [Pi.add_apply]; ring
  rw [hdec]
  refine hadd _ _ ?_ (fun _ _ _ => le_rfl) ?_ (hneg d)
  · intro j j' hjj'; simp only [Pi.add_apply]; have := hμ hjj'; omega
  · refine hnn (∑ j, (μ j + d)).toNat _ ?_ ?_ ?_
    · intro j j' hjj'; simp only [Pi.add_apply]; have := hμ hjj'; omega
    · intro j; simp only [Pi.add_apply]; have := hbound j; omega
    · simp only [Pi.add_apply]; exact Int.self_le_toNat _

end DiscreteGroups.sglob.LConvU
