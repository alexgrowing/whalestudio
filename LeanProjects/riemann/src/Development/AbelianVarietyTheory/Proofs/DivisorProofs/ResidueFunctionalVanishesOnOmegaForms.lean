import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowAdd

set_option autoImplicit false
noncomputable section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.ResVan

variable {F : Type} [Field F] {d : ℕ}

theorem prod_zpow_add (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j, x j ^ (m j + n j) = (∏ j, x j ^ m j) * ∏ j, x j ^ n j := by
  first
  | exact @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | (apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add ..)

def monoA (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) : Submonoid F where
  carrier := {f | ∃ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 ∧ (∀ j ∉ I, 0 ≤ m j) ∧ f = ∏ j, x j ^ m j}
  one_mem' := ⟨0, by simp, fun _ _ => le_rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, hm', rfl⟩ ⟨n, hn, hn', rfl⟩
    refine ⟨m + n, ?_, fun j hj => add_nonneg (hm' j hj) (hn' j hj), ?_⟩
    · simp [Finset.sum_add_distrib, hm, hn]
    · simp only [Pi.add_apply]; exact (prod_zpow_add x hx m n).symm

theorem prod_single_sub (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i j : Fin (d + 1)) :
    ∏ l, x l ^ ((Pi.single j 1 : Fin (d + 1) → ℤ) l - (Pi.single i 1 : Fin (d + 1) → ℤ) l) = x j / x i := by
  simp_rw [zpow_sub₀ (hx _)]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [Fintype.prod_eq_single j (fun l hl => by simp [Pi.single_apply, hl])]; simp
  · rw [Fintype.prod_eq_single i (fun l hl => by simp [Pi.single_apply, hl])]; simp

theorem prod_exp (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i0 : Fin (d + 1)) :
    (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ∏ j, x i0 / x j = 1 := by
  simp_rw [zpow_sub₀ (hx _), zpow_one]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hq : ∏ j, x j ^ (if j = i0 then ((d : ℤ) + 1) else 0) = x i0 ^ (d + 1) := by
    rw [Fintype.prod_eq_single i0 (fun l hl => by simp [hl])]
    rw [if_pos rfl, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : ∏ j, x j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hx j
  have h1 := hx i0
  field_simp

theorem resvan : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x →
    ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I →
    ∀ y ∈ omA k x I, ρ y = 0 := by
  intro k _ F _ _ d x hx ρ hρ i I hI hi y hy
  obtain ⟨i0, hi0⟩ := hI
  have hne := hx.ne
  have hii0 : i ≠ i0 := fun h => hi (h ▸ hi0)
  have h1 : (∏ j, x i0 / x j) * y ∈ rA k x I := by
    have h2 := (Submodule.mem_iInf _).1 hy i0
    have h3 := (Submodule.mem_iInf _).1 h2 hi0
    simpa using h3
  have hz : (∏ j, x i0 / x j) * y ∈ Submodule.span k (monoA x hne I : Set F) := by
    rw [rA, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h1
    refine Submodule.span_mono (Submonoid.closure_le.2 ?_) h1
    rintro _ ⟨i', hi', j, rfl⟩
    refine ⟨(Pi.single j 1 : Fin (d + 1) → ℤ) - Pi.single i' 1, by simp, fun l hl => ?_,
      (prod_single_sub x hne i' j).symm⟩
    have hl' : l ≠ i' := fun h => hl (h ▸ hi')
    simp only [Pi.sub_apply, Pi.single_apply, hl', if_false, sub_zero]
    split_ifs <;> omega
  have hP := prod_exp x hne i0
  have hy' : y = (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ((∏ j, x i0 / x j) * y) := by
    rw [← mul_assoc, hP, one_mul]
  rw [hy']
  generalize (∏ j, x i0 / x j) * y = z at hz
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, hm', rfl⟩ := hf
    rw [← prod_zpow_add x hne]
    refine hρ.2 _ ?_ ?_
    · rw [Finset.sum_add_distrib, hm, add_zero, Finset.sum_sub_distrib]
      simp
    · intro h0
      have := congrFun h0 i
      simp only [hii0, if_false, Pi.zero_apply] at this
      have := hm' i hi
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]

end GlobalTheory.PD.ResVan
