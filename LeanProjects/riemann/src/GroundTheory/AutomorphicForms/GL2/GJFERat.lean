import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLocalZeta

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Polynomial

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_norm_gt_eval_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℂ, B < ‖x‖ → Q.eval x ≠ 0 := by
  classical
  refine ⟨1 + ∑ r ∈ Q.roots.toFinset, ‖r‖, by positivity, fun x hx hQx => ?_⟩
  have hr : x ∈ Q.roots.toFinset := Multiset.mem_toFinset.2 ((mem_roots hQ).2 hQx)
  have := Finset.single_le_sum (f := fun r : ℂ => ‖r‖) (fun r _ => norm_nonneg r) hr
  linarith

theorem exists_denom_ne_zero_right (R : RatFunc ℂ) :
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → R.denom.eval (qs F s) ≠ 0 := by
  obtain ⟨ε, hε, h⟩ := exists_eval_ne_zero R.denom_ne_zero
  obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
  exact ⟨s₁, fun s hs => h _ (qs_ne_zero s) (hs₁ s hs)⟩

theorem exists_denom_ne_zero_left (R : RatFunc ℂ) :
    ∃ s₁ : ℝ, ∀ s : ℂ, s.re < -s₁ → R.denom.eval (qs F s) ≠ 0 := by
  obtain ⟨B, hB, h⟩ := exists_norm_gt_eval_ne_zero R.denom_ne_zero
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  refine ⟨Real.logb (LocalField.residueCard F) B, fun s hs => h _ ?_⟩
  rw [norm_qs]
  calc B = (LocalField.residueCard F : ℝ) ^ (Real.logb (LocalField.residueCard F) B) :=
        (Real.rpow_logb (by linarith) hq.ne' hB).symm
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)

theorem eq_of_eval_eq_of_infinite {R₁ R₂ : RatFunc ℂ} {S : Set ℂ} (hS : S.Infinite)
    (h : ∀ x ∈ S, R₁.eval (RingHom.id ℂ) x = R₂.eval (RingHom.id ℂ) x) : R₁ = R₂ := by
  classical
  set Q : ℂ[X] := R₁.num * R₂.denom - R₂.num * R₁.denom with hQdef
  have hne : R₁.denom * R₂.denom ≠ 0 := mul_ne_zero R₁.denom_ne_zero R₂.denom_ne_zero
  have hfin : {x : ℂ | (R₁.denom * R₂.denom).IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hne
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q ((hS.sdiff hfin).mono fun x hx => ?_)
    obtain ⟨hxS, hx0⟩ := hx
    simp only [Set.mem_ofPred_eq, IsRoot.def, eval_mul] at hx0
    have h1 : R₁.denom.eval x ≠ 0 := left_ne_zero_of_mul hx0
    have h2 : R₂.denom.eval x ≠ 0 := right_ne_zero_of_mul hx0
    have hx := h x hxS
    simp only [RatFunc.eval, eval₂_id] at hx
    rw [div_eq_div_iff h1 h2] at hx
    show eval x (R₁.num * R₂.denom - R₂.num * R₁.denom) = 0
    rw [eval_sub, eval_mul, eval_mul, hx, sub_self]
  rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero R₁.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero R₂.denom_ne_zero), ← map_mul, ← map_mul]
  rw [hQdef, sub_eq_zero] at hQ0
  rw [hQ0]

theorem eq_of_eval_qs_eq_right {R₁ R₂ : RatFunc ℂ} {s₁ : ℝ}
    (h : ∀ s : ℂ, s₁ < s.re →
      R₁.eval (RingHom.id ℂ) (qs F s) = R₂.eval (RingHom.id ℂ) (qs F s)) : R₁ = R₂ := by
  obtain ⟨ε, hε, hs⟩ := exists_qs_of_small (F := F) s₁
  exact eq_of_eval_eq hε fun x hx hxε => by
    obtain ⟨s, hs1, rfl⟩ := hs x hx hxε
    exact h s hs1

theorem eq_of_eval_qs_eq_left {R₁ R₂ : RatFunc ℂ} {s₁ : ℝ}
    (h : ∀ s : ℂ, s.re < s₁ →
      R₁.eval (RingHom.id ℂ) (qs F s) = R₂.eval (RingHom.id ℂ) (qs F s)) : R₁ = R₂ := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  set f : ℕ → ℂ := fun t => qs F (((s₁ - 1 - t : ℝ)) : ℂ) with hfdef
  have hinj : Function.Injective f := by
    intro t t' htt
    have hn := congrArg (‖·‖) htt
    simp only [hfdef, norm_qs, Complex.ofReal_re] at hn
    have hl := congrArg (Real.logb (LocalField.residueCard F)) hn
    rw [Real.logb_rpow (by linarith) hq.ne', Real.logb_rpow (by linarith) hq.ne'] at hl
    exact_mod_cast (by linarith : (t : ℝ) = t')
  refine eq_of_eval_eq_of_infinite (Set.infinite_range_of_injective hinj) ?_
  rintro _ ⟨t, rfl⟩
  refine h _ ?_
  simp only [Complex.ofReal_re]
  have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  linarith

variable (F) in

def RatFE (γ : RatFunc ℂ) (a b : ℂ → ℂ) : Prop :=
  ∃ (R : RatFunc ℂ) (s₁ : ℝ), (∀ s : ℂ, s₁ < s.re → a s = R.eval (RingHom.id ℂ) (qs F s)) ∧
    ∀ s : ℂ, s.re < -s₁ → b s = (γ * R).eval (RingHom.id ℂ) (qs F s)

namespace RatFE

variable {γ γ' γ₁ γ₂ : RatFunc ℂ} {a b a₁ a₂ b₁ b₂ : ℂ → ℂ}

theorem congr {a' b' : ℂ → ℂ} (h : RatFE F γ a b) (ha : ∃ t : ℝ, ∀ s : ℂ, t < s.re → a' s = a s)
    (hb : ∃ t : ℝ, ∀ s : ℂ, s.re < t → b' s = b s) : RatFE F γ a' b' := by
  obtain ⟨R, s₁, h₁, h₂⟩ := h
  obtain ⟨t, ht⟩ := ha
  obtain ⟨u, hu⟩ := hb
  refine ⟨R, max s₁ (max t (-u)), fun s hs => ?_, fun s hs => ?_⟩
  · simp only [max_lt_iff] at hs
    rw [ht s hs.2.1, h₁ s hs.1]
  · have h1 : s.re < -s₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
    have h2 : s.re < u := by
      have : -max s₁ (max t (-u)) ≤ u := by
        have := le_max_right s₁ (max t (-u))
        have := le_max_right t (-u)
        linarith
      linarith
    rw [hu s h2, h₂ s h1]

theorem zero : RatFE F γ (fun _ => 0) (fun _ => 0) :=
  ⟨0, 0, fun _ _ => by simp, fun _ _ => by simp⟩

theorem add (h₁ : RatFE F γ a₁ b₁) (h₂ : RatFE F γ a₂ b₂) :
    RatFE F γ (fun s => a₁ s + a₂ s) (fun s => b₁ s + b₂ s) := by
  obtain ⟨R₁, s₁, ha₁, hb₁⟩ := h₁
  obtain ⟨R₂, s₂, ha₂, hb₂⟩ := h₂
  obtain ⟨t₁, ht₁⟩ := exists_denom_ne_zero_right (F := F) R₁
  obtain ⟨t₂, ht₂⟩ := exists_denom_ne_zero_right (F := F) R₂
  obtain ⟨u₁, hu₁⟩ := exists_denom_ne_zero_left (F := F) (γ * R₁)
  obtain ⟨u₂, hu₂⟩ := exists_denom_ne_zero_left (F := F) (γ * R₂)
  set M := max (max s₁ s₂) (max (max t₁ t₂) (max u₁ u₂)) with hM
  have hs₁ : s₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs₂ : s₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have ht₁' : t₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have ht₂' : t₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hu₁' : u₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hu₂' : u₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨R₁ + R₂, M, fun s hs => ?_, fun s hs => ?_⟩
  · show a₁ s + a₂ s = _
    rw [ha₁ s (by linarith), ha₂ s (by linarith),
      RatFunc.eval_add (hx := ht₁ s (by linarith)) (hy := ht₂ s (by linarith))]
  · show b₁ s + b₂ s = _
    rw [hb₁ s (by linarith), hb₂ s (by linarith), mul_add,
      RatFunc.eval_add (hx := hu₁ s (by linarith)) (hy := hu₂ s (by linarith))]

theorem const_mul (c : ℂ) (h : RatFE F γ a b) :
    RatFE F γ (fun s => c * a s) (fun s => c * b s) := by
  obtain ⟨R, s₁, ha, hb⟩ := h
  have hC : ∀ x : ℂ, (RatFunc.C c).denom.eval₂ (RingHom.id ℂ) x ≠ 0 := fun x => by
    rw [RatFunc.denom_C]; simp
  obtain ⟨t, ht⟩ := exists_denom_ne_zero_right (F := F) R
  obtain ⟨u, hu⟩ := exists_denom_ne_zero_left (F := F) (γ * R)
  refine ⟨RatFunc.C c * R, max s₁ (max t u), fun s hs => ?_, fun s hs => ?_⟩
  · simp only [max_lt_iff] at hs
    show c * a s = _
    rw [ha s hs.1, RatFunc.eval_mul (hx := hC _) (hy := ht s hs.2.1), RatFunc.eval_C]
    rfl
  · have h1 : s.re < -s₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
    have h2 : s.re < -u := lt_of_lt_of_le hs
      (neg_le_neg (le_trans (le_max_right _ _) (le_max_right _ _)))
    show c * b s = _
    rw [hb s h1, show γ * (RatFunc.C c * R) = RatFunc.C c * (γ * R) by ring,
      RatFunc.eval_mul (hx := hC _) (hy := hu s h2), RatFunc.eval_C]
    rfl

theorem sum {ι : Type*} (s : Finset ι) {a b : ι → ℂ → ℂ} (h : ∀ i ∈ s, RatFE F γ (a i) (b i)) :
    RatFE F γ (fun z => ∑ i ∈ s, a i z) (fun z => ∑ i ∈ s, b i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (F := F) (γ := γ))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem mul (h₁ : RatFE F γ₁ a₁ b₁) (h₂ : RatFE F γ₂ a₂ b₂) :
    RatFE F (γ₁ * γ₂) (fun s => a₁ s * a₂ s) (fun s => b₁ s * b₂ s) := by
  obtain ⟨R₁, s₁, ha₁, hb₁⟩ := h₁
  obtain ⟨R₂, s₂, ha₂, hb₂⟩ := h₂
  obtain ⟨t₁, ht₁⟩ := exists_denom_ne_zero_right (F := F) R₁
  obtain ⟨t₂, ht₂⟩ := exists_denom_ne_zero_right (F := F) R₂
  obtain ⟨u₁, hu₁⟩ := exists_denom_ne_zero_left (F := F) (γ₁ * R₁)
  obtain ⟨u₂, hu₂⟩ := exists_denom_ne_zero_left (F := F) (γ₂ * R₂)
  set M := max (max s₁ s₂) (max (max t₁ t₂) (max u₁ u₂)) with hM
  have hs₁ : s₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs₂ : s₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have ht₁' : t₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have ht₂' : t₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hu₁' : u₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hu₂' : u₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨R₁ * R₂, M, fun s hs => ?_, fun s hs => ?_⟩
  · show a₁ s * a₂ s = _
    rw [ha₁ s (by linarith), ha₂ s (by linarith),
      RatFunc.eval_mul (hx := ht₁ s (by linarith)) (hy := ht₂ s (by linarith))]
  · show b₁ s * b₂ s = _
    rw [hb₁ s (by linarith), hb₂ s (by linarith),
      show γ₁ * γ₂ * (R₁ * R₂) = (γ₁ * R₁) * (γ₂ * R₂) by ring,
      RatFunc.eval_mul (hx := hu₁ s (by linarith)) (hy := hu₂ s (by linarith))]

theorem unique (h : RatFE F γ a b) (h' : RatFE F γ' a b)
    (ha : ∀ t : ℝ, ∃ s : ℂ, t < s.re ∧ a s ≠ 0) : γ = γ' := by
  obtain ⟨R, s₁, ha₁, hb₁⟩ := h
  obtain ⟨R', s₁', ha₁', hb₁'⟩ := h'
  have hRR : R = R' := eq_of_eval_qs_eq_right (F := F) (s₁ := max s₁ s₁') fun s hs => by
    rw [max_lt_iff] at hs
    rw [← ha₁ s hs.1, ha₁' s hs.2]
  subst hRR
  have hR : R ≠ 0 := by
    rintro rfl
    obtain ⟨s, hs, hne⟩ := ha s₁
    exact hne (by rw [ha₁ s hs]; simp)
  have hγ : γ * R = γ' * R := eq_of_eval_qs_eq_left (F := F) (s₁ := min (-s₁) (-s₁')) fun s hs => by
    rw [lt_min_iff] at hs
    rw [← hb₁ s hs.1, hb₁' s hs.2]
  exact mul_right_cancel₀ hR hγ

end RatFE

end GodementJacquet

end GroundTheory.Automorphic
