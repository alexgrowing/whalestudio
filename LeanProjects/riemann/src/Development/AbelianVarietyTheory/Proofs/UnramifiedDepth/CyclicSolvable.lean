import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.FlowProgramme

lemma sum_shift (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma duality (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => h2 a
  rw [Finset.sum_add_distrib, sum_shift] at hs
  have hT : 0 ≤ ∑ a, ∑ i ∈ Finset.range d, x a i :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => h0 a i
  constructor
  · have : (l : ℝ) * ∑ a, ∑ i ∈ Finset.range d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : x a i = 0
      · simp [h]
      · have hi : i ≠ 0 := by
          rintro rfl
          exact absurd (h1 a 0 h).1 (by decide)
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi) (h0 a i)
    linarith
  · intro i₀
    have hp : (0 : ℝ) < (l : ℝ) ^ i₀ := by positivity
    rw [le_inv_mul_iff₀ hp]
    have : (l : ℝ) ^ i₀ * ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i₀ * x a i
          ≤ ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i * x a i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (Finset.mem_Ico.1 hi).1) (h0 a i)
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (by positivity) (h0 a i)
            intro i hi
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    linarith

lemma cyclic_nonneg (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min y
  obtain ⟨a₁, h₁⟩ := Finite.exists_max y
  refine le_trans ?_ (h₀ a)
  have e0 := hy a₀
  have e1 := hy a₁
  have f0 := h₁ (a₀ - 1)
  have f1 := h₀ (a₁ - 1)
  have g := hX a₁ a₀
  have k : l * y (a₀ - 1) ≤ l * y a₁ := mul_le_mul_of_nonneg_left f0 (by linarith)
  have k2 : 0 ≤ (l * l - 1) * y a₀ := by rw [← e0] at g; nlinarith
  have k3 : 0 < l * l - 1 := by nlinarith
  exact (mul_nonneg_iff_of_pos_left k3).1 k2

lemma cyclic_solvable (l : ℝ) (d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) :
    ∃ y : ZMod d → ℝ, ∀ a, l * y a + y (a - 1) = X a := by
  let T : (ZMod d → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun y a => l * y a + y (a - 1)
      map_add' := fun y z => by ext a; simp; ring
      map_smul' := fun c y => by ext a; simp; ring }
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : ∀ a, l * y a + y (a - 1) = 0 := fun a => congrFun hy a
    ext a
    have h1 := cyclic_nonneg l d (fun _ => 0) y hl (by simp) hy' a
    have h2 := cyclic_nonneg l d (fun _ => 0) (fun a => - y a) hl (by simp)
      (fun a => by have := hy' a; linarith) a
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj X
  exact ⟨y, fun a => congrFun hy a⟩

lemma balanced (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hd : 2 ≤ d)
    (hX : ∀ a b, X a ≤ l * X b) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧
      ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨y, hy⟩ := cyclic_solvable l d X hl'
  have hpos := cyclic_nonneg l d X y hl' hX hy
  have h1 : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun a i => if i = 1 then y a else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a i
    dsimp only
    split_ifs
    · exact hpos a
    · exact le_rfl
  · intro a i h
    dsimp only at h
    split_ifs at h with hi
    · subst hi
      exact ⟨odd_one, by omega⟩
    · exact absurd rfl h
  · intro a
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', h1, if_true, pow_one, Nat.cast_one]
    exact (hy a).le
  · simp only [Finset.sum_ite_eq', h1, if_true]
    have : ∑ a, y (a - 1) = ∑ a, y a := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [← Finset.sum_congr rfl fun a _ => hy a, Finset.sum_add_distrib, this, ← Finset.mul_sum]
    ring

lemma optimum (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hX : ∀ a, 0 ≤ X a) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ∀ x' : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x' a i) ∧ (∀ a i, x' a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x' a i + ∑ i ∈ Finset.range d, x' (a - i) i ≤ X a) →
      ∑ a, ∑ i ∈ Finset.range d, x' a i ≤ ∑ a, ∑ i ∈ Finset.range d, x a i := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  let S : Set (ZMod d → ℕ → ℝ) := {x | ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)}
  have hclosed : IsClosed S := by
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun a => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)
    · refine isClosed_iInter fun a => isClosed_iInter fun i => ?_
      by_cases h : Odd i ∧ i < d
      · convert isClosed_univ
        ext x
        simp [h]
      · have hc : IsClosed {x : ZMod d → ℕ → ℝ | x a i = 0} :=
          isClosed_eq (by fun_prop) continuous_const
        convert hc
        tauto
    · exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun a : ZMod d =>
      Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (X a)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : IsCompact S := by
    refine hK.of_isClosed_subset hclosed ?_
    rintro x ⟨h0, h1, h2⟩ a - i -
    refine ⟨h0 a i, ?_⟩
    by_cases h : x a i = 0
    · rw [h]; exact hX a
    · have hi := Finset.mem_range.2 (h1 a i h).2
      have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i :=
        Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
          (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
      have e2 : 0 ≤ ∑ i ∈ Finset.range d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
      have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
      have := h2 a
      linarith
  have hne : S.Nonempty := ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ h => absurd rfl h,
    fun a => by simpa using hX a⟩
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
    (f := fun x => ∑ a, ∑ i ∈ Finset.range d, x a i) (Continuous.continuousOn (by fun_prop))
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

theorem main :
  (∀ (l d : ℕ) [NeZero d] (X : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ X a) →
    (∀ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) → ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a) ∧
    (2 ≤ d → (∀ a b, X a ≤ l * X b) → ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a) ∧
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ∀ x' : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x' a i) ∧ (∀ a i, x' a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x' a i + ∑ i ∈ Finset.range d, x' (a - i) i ≤ X a) → ∑ a, ∑ i ∈ Finset.range d, x' a i ≤ ∑ a, ∑ i ∈ Finset.range d, x a i) := by
  intro l d _ X hl hX
  exact ⟨duality l d X hl, balanced l d X hl, optimum l d X hl hX⟩

end GlobalTheory.FlowProgramme
