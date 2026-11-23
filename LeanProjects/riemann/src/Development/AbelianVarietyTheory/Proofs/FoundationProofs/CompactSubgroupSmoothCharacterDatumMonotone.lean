import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactModStabilizer
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.StripGrp

variable {k : Type} [Field k] [ValuativeRel k]

theorem triv_mono {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y :=
  fun u hu h1 => hx u hu (h1.trans h)

theorem triv_add {χ : kˣ →* ℂˣ} {x y : k} (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le h le_rfl)) hy
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le le_rfl h)) hx

theorem triv_neg {χ : kˣ →* ℂˣ} {x : k} (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono (by rw [Valuation.map_neg]) hx

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h1
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h1) zero_le'
  have hu : u = 1 := Units.ext (sub_eq_zero.mp ((Valuation.zero_iff _).mp h0))
  simp [hu]

theorem le_inv_of_mul_le {a b : ValueGroupWithZero k} (ha : a ≠ 0) (h : a * b ≤ 1) : b ≤ a⁻¹ :=
  calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left₀ ha b).symm
    _ ≤ a⁻¹ * 1 := by gcongr
    _ = a⁻¹ := mul_one _

variable {n : ℕ}

theorem ne_of_blk {r : ℕ} {i j : Fin n} (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) : i ≠ j := by
  rintro rfl; omega

theorem val_one_apply_le (i j : Fin n) : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mul_eq_zero_of_blk {r : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → A i j = 0)
    (hB : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → B i j = 0) : A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < r
  · rw [hA i l (fun h => absurd h.2 (not_le.mpr hl)), zero_mul]
  · rw [hB l j (fun h => hl h.1), mul_zero]

variable {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ}

theorem mem_strip {g : GL (Fin n) k} : g ∈ strip ψ r ϖ m ↔ ∀ i j : Fin n,
    if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := Iff.rfl

theorem sub_one_of_mem {g : GL (Fin n) k} (hg : g ∈ strip ψ r ϖ m) (i j : Fin n)
    (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : (g.val - 1) i j = 0 := by
  have := mem_strip.mp hg i j
  rw [if_neg h] at this
  simp [Matrix.sub_apply, this]

theorem one_mem : (1 : GL (Fin n) k) ∈ strip ψ r ϖ m := by
  intro i j
  split_ifs with h
  · simp only [Units.val_one, Matrix.one_apply_ne (ne_of_blk h), mul_zero, map_zero, zero_le',
      true_and]
    exact triv_zero _
  · rfl

theorem mul_mem {a b : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) (hb : b ∈ strip ψ r ϖ m) :
    a * b ∈ strip ψ r ϖ m := by
  have key : (a * b).val = 1 + (a.val - 1) + (b.val - 1) := by
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem hb)
    rw [Units.val_mul]
    calc a.val * b.val = (1 + (a.val - 1)) * (1 + (b.val - 1)) := by simp
      _ = 1 + (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  have hB := mem_strip.mp hb i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA hB
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.add_apply, Matrix.sub_apply, h1, sub_zero, zero_add]
    rw [mul_add]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le hA.1 hB.1), triv_add hA.2 hB.2⟩
  · rw [if_neg h] at hA hB
    simp only [Matrix.add_apply, Matrix.sub_apply, hA, hB, sub_self, add_zero]

theorem inv_mem {a : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) : a⁻¹ ∈ strip ψ r ϖ m := by
  have key : (a⁻¹).val = 1 - (a.val - 1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem ha)
    calc a.val * (1 - (a.val - 1)) = 1 - (a.val - 1) * (a.val - 1) := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.sub_apply, h1, sub_zero, zero_sub, mul_neg, Valuation.map_neg]
    exact ⟨hA.1, triv_neg hA.2⟩
  · rw [if_neg h] at hA
    simp only [Matrix.sub_apply, hA, sub_self, sub_zero]

theorem mono {m m' : ℕ} (hϖ : valuation k ϖ < 1) (hmm : m ≤ m') :
    strip ψ r ϖ m ⊆ strip ψ r ϖ m' := by
  intro g hg i j
  have hA := mem_strip.mp hg i j
  split_ifs with h
  · rw [if_pos h] at hA
    have hle : valuation k (ϖ ^ m' * g.val i j) ≤ valuation k (ϖ ^ m * g.val i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      gcongr ?_ * _
      exact pow_le_pow_right_of_le_one' hϖ.le hmm
    exact ⟨hle.trans hA.1, triv_mono hle hA.2⟩
  · rwa [if_neg h] at hA

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_triv (χ : kˣ →* ℂˣ) : IsClosed {x : k | Triv χ x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation k x ≠ 0 := fun h0 => hx (by
    have : x = 0 := (Valuation.zero_iff _).mp h0
    rw [this]; exact triv_zero χ)
  refine Filter.mem_of_superset ((valuation k).locally_const hx0) ?_
  intro y hy hT
  exact hx (triv_mono (le_of_eq hy.symm) hT)

theorem isClosed_strip : IsClosed (strip ψ r ϖ m) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hball : IsClosed {z : k | valuation k z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed
  have hS : IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ i j : Fin n,
      if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * A i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * A i j)
      else A i j = (1 : Matrix (Fin n) (Fin n) k) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) k => A i j :=
      (continuous_apply j).comp (continuous_apply i)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [if_pos h]
      exact (hball.inter (isClosed_triv _)).preimage (continuous_const.mul hc)
    · simp only [if_neg h]
      exact isClosed_eq hc continuous_const
  exact hS.preimage Units.continuous_val

theorem isCompact_strip (hϖ0 : ϖ ≠ 0) (hϖ : valuation k ϖ < 1) : IsCompact (strip ψ r ϖ m) := by
  set a := valuation k (ϖ ^ m) with ha_def
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hϖ0)
  have ha1 : a ≤ 1 := by rw [ha_def, map_pow]; exact pow_le_one' hϖ.le _
  have h1t : (1 : ValueGroupWithZero k) ≤ a⁻¹ := le_inv_of_mul_le ha0 (by rw [mul_one]; exact ha1)
  have hbd : ∀ g ∈ strip ψ r ϖ m, ∀ i j : Fin n, valuation k (g.val i j) ≤ a⁻¹ := by
    intro g hg i j
    have hA := mem_strip.mp hg i j
    split_ifs at hA with h
    · exact le_inv_of_mul_le ha0 (by rw [ha_def, ← map_mul]; exact hA.1)
    · rw [hA]; exact (val_one_apply_le i j).trans h1t
  refine (GlobalTheory.PairingOne.isCompact_bounded (m := Fin n) a⁻¹).of_isClosed_subset isClosed_strip ?_
  intro g hg
  exact ⟨hbd g hg, hbd g⁻¹ (inv_mem hg)⟩

theorem strip_datum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  intro k _ _ _ _ n ψ r ϖ _ hϖ0 hϖ _
  refine ⟨fun m => ⟨one_mem, fun a ha b hb => mul_mem ha hb, fun a ha => inv_mem ha,
    isCompact_strip hϖ0 hϖ, rfl, fun _ _ _ _ => (mul_one 1).symm,
    ⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩⟩, fun m m' hmm => mono hϖ hmm⟩

end GlobalTheory.StripGrp
