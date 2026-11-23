import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

def boxExp {n n' : Type} {c : ℕ} : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → ℕ
  | (_, Sum.inl _) => 0
  | (Sum.inl _, Sum.inr j) => j.val
  | (Sum.inr l, Sum.inr j) => j.val - (l.val + 1)

theorem boxExp_eq_zero {n n' : Type} {c : ℕ} (rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
    (h : ¬ Free 1 rs) : boxExp rs = 0 := by
  rcases rs with ⟨r | l, s | j⟩ <;> simp only [Free, boxExp] at h ⊢ <;> omega

theorem sum_fin_sub (c j : ℕ) (hj : j ≤ c) :
    ∑ l : Fin c, (j - (l.val + 1)) = j * (j - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => j - (l + 1)) c]
  have h1 : ∑ l ∈ Finset.range c, (j - (l + 1)) = ∑ l ∈ Finset.range j, (j - (l + 1)) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 hj) ?_
    intro x _ hx
    simp only [Finset.mem_range] at hx
    omega
  rw [h1, ← Finset.sum_range_id, ← Finset.sum_range_reflect (fun i => i) j]
  refine Finset.sum_congr rfl fun x _ => by omega

theorem sum_boxExp (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    ∑ rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), boxExp rs = expo c (Fintype.card n) := by
  rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, boxExp, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h : ∀ j : Fin (c + 1), Fintype.card n * j.val + ∑ l : Fin c, (j.val - (l.val + 1))
      = j.val * Fintype.card n + j.val * (j.val - 1) / 2 := by
    intro j
    rw [sum_fin_sub c j (by omega), mul_comm]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range (fun j => j * Fintype.card n + j * (j - 1) / 2) (c + 1), expo]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    obtain rfl : x = 0 := by omega
    simp

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem measure_pow_mul_mem [MeasurableSpace k] [BorelSpace k] {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ)
    (ν : Measure k) (hν : IsUnitVol ν) (m : ℕ) :
    ν {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = (resCard k : ENNReal) ^ m := by
  have := hν.1
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (ϖ : k) h0 with hu
  have hset : {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = cball (u⁻¹ ^ m) := by
    ext x
    have hv : 0 < valuation k (ϖ : k) ^ m := pow_pos ((Valuation.pos_iff _).2 h0) m
    simp only [Set.mem_ofPred_eq, cball, Valuation.mem_integer_iff, map_mul, map_pow, hu,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow]
    rw [← one_div, le_div_iff₀ hv, mul_comm]
  have h1 : distribHaarChar k u⁻¹ = (resCard k : NNReal) := by
    have := nabs_uniformiser hϖ (x := u) rfl
    rw [map_inv]
    apply NNReal.coe_injective
    rw [NNReal.coe_inv]
    simp only [nabs] at this
    rw [this]
    simp
  rw [hset, measure_cball, hν.2, mul_one, map_pow, h1]
  simp

theorem perLat_stdLat_eq {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) :
    ((perLat ϖ n' c (stdLat k n) : AddSubgroup _) :
      Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) =
      Set.univ.pi fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} =>
        {x | (ϖ : k) ^ boxExp rs.1 * x ∈ 𝒪[k]} := by
  have key : ∀ (i l : ℕ) (x : k), l ≤ i →
      ((∃ a : 𝒪[k], (ϖ : k) ^ (i + 1) * x = a * (ϖ : k) ^ (l + 1)) ↔
        (ϖ : k) ^ (i + 1 - (l + 1)) * x ∈ 𝒪[k]) := by
    intro i l x hl
    have hp : (ϖ : k) ^ (i + 1) = (ϖ : k) ^ (i + 1 - (l + 1)) * (ϖ : k) ^ (l + 1) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · rintro ⟨a, ha⟩
      have : (ϖ : k) ^ (i + 1 - (l + 1)) * x = a := by
        apply mul_right_cancel₀ (pow_ne_zero (l + 1) h0)
        rw [← ha, hp]; ring
      rw [this]; exact a.2
    · intro h
      exact ⟨⟨_, h⟩, by rw [hp]; ring⟩
  ext e
  simp only [SetLike.mem_coe, mem_perLat, mem_chainLat, mem_stdLat, Set.mem_pi, Set.mem_univ,
    Set.mem_ofPred_eq, forall_true_left, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro h ⟨⟨r, s | j⟩, hf⟩
    · rcases r with r | l <;> simp [Free] at hf
    · have hj : j ≠ 0 := by
        rintro rfl
        rcases r with r | l <;> simp [Free] at hf
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
      rcases r with r | l
      · have := (h i).1 r
        simp only [UnfoldShape.col, dif_pos hf] at this
        exact this
      · have := (h i).2 l
        simp only [UnfoldShape.col, dif_pos hf] at this
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).1 this
  · intro h i
    refine ⟨fun r => ?_, fun l => ?_⟩
    · have hf : Free 1 ((Sum.inl r, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
        simp [Free]
      simp only [UnfoldShape.col, dif_pos hf]
      exact h ⟨_, hf⟩
    · by_cases hf : Free 1 ((Sum.inr l, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
      · simp only [UnfoldShape.col, dif_pos hf]
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).2 (h ⟨_, hf⟩)
      · simp only [UnfoldShape.col, dif_neg hf]
        exact ⟨0, by simp⟩

end

theorem volFree_perLat_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (ν : Measure k) (hν : IsUnitVol ν) :
    volFree ν n n' c (perLat ϖ n' c (stdLat k n))
      = (resCard k : ENNReal) ^ expo c (Fintype.card n) := by
  classical
  have := hν.1
  have := secondCountable k
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [perLat_stdLat_eq h0, volFree, Measure.pi_pi]
  simp only [measure_pow_mul_mem hϖ ν hν]
  rw [Finset.prod_pow_eq_pow_sum, ← sum_boxExp n n' c]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter fun rs => Free 1 rs) (by simp) boxExp]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => boxExp_eq_zero x ?_
  simpa using hx

end GlobalTheory.RootEx.UnfoldShape
