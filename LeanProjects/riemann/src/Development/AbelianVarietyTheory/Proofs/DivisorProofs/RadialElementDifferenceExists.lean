import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo.TransStable

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ex (x : k) : ℤ := WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k x))

theorem exp_ex {x : k} (hx : x ≠ 0) :
    WithZero.exp (ex x) = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k x) := by
  apply WithZero.exp_log
  simpa using hx

theorem val_le_iff {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    valuation k x ≤ valuation k y ↔ ex x ≤ ex y := by
  rw [← map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k), ← exp_ex hx, ← exp_ex hy,
    WithZero.exp_le_exp]

theorem val_lt_iff {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    valuation k x < valuation k y ↔ ex x < ex y := by
  rw [← map_lt_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k), ← exp_ex hx, ← exp_ex hy,
    WithZero.exp_lt_exp]

theorem ex_mul {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) : ex (x * y) = ex x + ex y := by
  unfold ex
  rw [map_mul, map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, ex (ϖ : k) = -1 := by
  obtain ⟨x, hx⟩ := valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k).symm (WithZero.exp (-1)))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    have h := congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k) hx
    rw [map_zero, OrderMonoidIso.apply_symm_apply] at h
    exact WithZero.exp_ne_zero h.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  simp only [Units.val_mk0, ex, hx, OrderMonoidIso.apply_symm_apply, WithZero.log_exp]

theorem val_lt_iff_le_unif {ϖ : kˣ} (hϖ : ex (ϖ : k) = -1) (x : k) {y : k} (hy : y ≠ 0) :
    valuation k x < valuation k y ↔ valuation k x ≤ valuation k ((ϖ : k) * y) := by
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, zero_le', iff_true]
    exact (Valuation.pos_iff _).2 hy
  · rw [val_lt_iff hx hy, val_le_iff hx (mul_ne_zero ϖ.ne_zero hy), ex_mul ϖ.ne_zero hy, hϖ]
    omega

end GlobalTheory.PrinTwo.TransStable

open GlobalTheory.PrinTwo.TransStable in

theorem GlobalTheory.PrinTwo.exists_smul_elemDiff_mem_of_radial : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)),
    (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → ∀ R ∈ W, GlobalTheory.PrinTwo.IsLC R → GlobalTheory.PrinTwo.IsCS R →
    R 0 ≠ 0 → (∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x) →
    ∃ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 ∧ ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y ∧
      c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W := by
  intro k _ _ _ _ W hW R hR hLC hCS hR0 hrad
  obtain ⟨r₀, hr₀⟩ := hLC
  obtain ⟨R₁, hR₁⟩ := hCS

  have hv : ∀ x y : k, valuation k x = valuation k y → R x = R y := by
    intro x y hxy
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, eq_comm, Valuation.zero_iff] at hxy
      rw [hxy]
    · have hy : y ≠ 0 := by
        rintro rfl
        rw [map_zero, Valuation.zero_iff] at hxy
        exact hx hxy
      have hu : valuation k ((Units.mk0 (y / x) (div_ne_zero hy hx) : kˣ) : k) = 1 := by
        rw [Units.val_mk0, map_div₀, hxy, div_self ((Valuation.ne_zero_iff _).2 hy)]
      have := hrad _ x hu
      rw [Units.val_mk0, div_mul_cancel₀ y hx] at this
      exact this.symm
  obtain ⟨ϖ, hϖ⟩ := exists_unif k

  let P : ℤ → Prop := fun n => ∃ y : k, y ≠ 0 ∧ R y ≠ R 0 ∧ ex y = n
  have hbdd : ∃ b, ∀ z, P z → b ≤ z := by
    refine ⟨ex (r₀ : k), ?_⟩
    rintro z ⟨y, hy0, hy, rfl⟩
    by_contra hlt
    push_neg at hlt
    apply hy
    have := hr₀ 0 y ((val_le_iff hy0 r₀.ne_zero).2 hlt.le)
    simpa using this
  have hne : ∃ z, P z := by
    have hy0 : ((ϖ⁻¹ : kˣ) : k) * (R₁ : k) ≠ 0 := mul_ne_zero (Units.ne_zero _) R₁.ne_zero
    refine ⟨_, _, hy0, ?_, rfl⟩
    have hlt : valuation k (R₁ : k) < valuation k (((ϖ⁻¹ : kˣ) : k) * (R₁ : k)) := by
      rw [val_lt_iff_le_unif hϖ _ hy0, Units.mul_inv_cancel_left]
    intro h
    rw [hR₁ _ hlt] at h
    exact hR0 h.symm
  obtain ⟨n, ⟨y₀, hy₀0, hy₀, rfl⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hne

  have hbelow : ∀ x : k, valuation k x < valuation k y₀ → R x = R 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
    · by_contra h
      have := hmin _ ⟨x, hx0, h, rfl⟩
      rw [val_lt_iff hx0 hy₀0] at hx
      omega

  have hinv : ∀ x z : k, valuation k z < valuation k y₀ → R (x + z) = R x := by
    intro x z hz
    rcases lt_or_ge (valuation k x) (valuation k y₀) with hx | hx
    · rw [hbelow x hx, hbelow _ (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hz))]
    · exact hv _ _ (Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_le hz hx))
  let r : kˣ := ϖ * Units.mk0 y₀ hy₀0
  have hr : ∀ z : k, valuation k z ≤ valuation k (r : k) ↔ valuation k z < valuation k y₀ := fun z => by
    rw [val_lt_iff_le_unif hϖ z hy₀0]
    simp [r]
  have hrlt : valuation k (r : k) < valuation k y₀ := (hr r).1 le_rfl
  refine ⟨y₀, r, R (-y₀) - R 0, ?_, hrlt, ?_⟩
  · rw [sub_ne_zero, hv (-y₀) y₀ (Valuation.map_neg _ _)]
    exact hy₀
  · have hmem : (fun x => R (x + -y₀)) - R ∈ W := W.sub_mem (hW R hR (-y₀)) hR
    convert hmem using 1
    funext x
    simp only [GlobalTheory.PrinTwo.elemDiff, GlobalTheory.PrinTwo.ball, Pi.smul_apply, Pi.sub_apply, Set.indicator_apply,
      Set.mem_setOf_eq, sub_zero, Pi.one_apply, smul_eq_mul]
    simp only [hr]
    by_cases h1 : valuation k x < valuation k y₀
    · have h2 : ¬ valuation k (x - y₀) < valuation k y₀ := by
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rwa [Valuation.map_neg]),
          Valuation.map_neg]
        exact lt_irrefl _
      rw [if_pos h1, if_neg h2, add_comm, hinv (-y₀) x h1, hbelow x h1]
      ring
    · by_cases h2 : valuation k (x - y₀) < valuation k y₀
      · have e1 : R (x + -y₀) = R 0 := by rw [← sub_eq_add_neg]; exact hbelow _ h2
        have e2 : R x = R (-y₀) := by
          rw [show x = y₀ + (x - y₀) by ring, hinv y₀ _ h2]
          exact hv _ _ (Valuation.map_neg _ _).symm
        rw [if_neg h1, if_pos h2, e1, e2]
        ring
      · push_neg at h1 h2
        have e : valuation k (x + -y₀) = valuation k x := by
          rw [← sub_eq_add_neg]
          apply le_antisymm
          · exact (Valuation.map_sub _ _ _).trans (max_le le_rfl h1)
          · calc valuation k x = valuation k ((x - y₀) + y₀) := by rw [sub_add_cancel]
              _ ≤ max (valuation k (x - y₀)) (valuation k y₀) := Valuation.map_add _ _ _
              _ ≤ valuation k (x - y₀) := max_le le_rfl h2
        rw [if_neg (not_lt.2 h1), if_neg (not_lt.2 h2), hv _ _ e]
        ring
