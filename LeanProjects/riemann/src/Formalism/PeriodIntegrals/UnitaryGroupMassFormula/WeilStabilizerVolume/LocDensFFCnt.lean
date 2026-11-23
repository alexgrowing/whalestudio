import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFHS

noncomputable section

namespace PI.VolStabW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  have : (h e e)⁻¹ * h e x * h e e = h e x := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  rw [mem_perp, hs.sub_right, hs.smul_right, this, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  let E1 : {x : V // h x x = c} ≃
      {p : K × perp hs e // h p.2 p.2 = c - σ p.1 * p.1 * h e e} :=
    { toFun := fun x => ⟨((h e e)⁻¹ * h e x.1, ⟨_, perp_sub_mem hs e x.1 he⟩), by
        have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
        have := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
        rw [add_sub_cancel, x.2] at this
        simp only
        linear_combination -this⟩
      invFun := fun p => ⟨p.1.1 • e + p.1.2, by
        rw [decomp_val hs e _ ((mem_perp hs e _).1 p.1.2.2), p.2]; ring⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel _ _)
      right_inv := by
        rintro ⟨⟨t, w⟩, hw⟩
        have hew : h e w = 0 := (mem_perp hs e w).1 w.2
        have ht : (h e e)⁻¹ * h e (t • e + (w : V)) = t := by
          rw [hs.add_right, hs.smul_right, hew, add_zero, mul_comm, mul_assoc,
            mul_inv_cancel₀ he, mul_one]
        apply Subtype.ext
        apply Prod.ext
        · exact ht
        · apply Subtype.ext
          show t • e + (w : V) - ((h e e)⁻¹ * h e (t • e + (w : V))) • e = w
          rw [ht, add_sub_cancel_left] }
  rw [Nat.card_congr (E1.trans (Equiv.subtypeProdEquivSigmaSubtype
    (fun t (w : perp hs e) => h w w = c - σ t * t * h e e))), Nat.card_sigma]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm c _
    have : Subsingleton V := Module.finrank_zero_iff.1 hm
    by_cases hc : c = 0
    · have h1 : Nat.card {x : V // h x x = c} = 1 := Nat.card_eq_one_iff_exists.2
        ⟨⟨0, by rw [hs.toIsSq.zero_left, hc]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [h1, if_pos hc]
      simp only [Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_sub, pow_zero, one_mul]
      rw [zpow_neg_one, ← mul_one_add, add_sub_cancel, inv_mul_cancel₀ hq']
    · have : IsEmpty {x : V // h x x = c} := ⟨fun ⟨x, hx⟩ => hc (by
        rw [← hx, Subsingleton.elim x 0, hs.toIsSq.zero_left])⟩
      rw [Nat.card_of_isEmpty, if_neg hc]
      simp
  | succ m ih =>
    intro V _ _ _ h hs hm c hc
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    rw [card_decomp hq e he c, Nat.cast_sum]
    have hfix : ∀ t : K, σ (c - σ t * t * h e e) = c - σ t * t * h e e := fun t => by
      rw [map_sub, map_mul, map_mul, hσ, hc, hq.self_fixed]; ring
    rw [Finset.sum_congr rfl (fun t _ => ih (perp hq e) (fun w w' => h w w')
      (perp_isHS hs e he) hfr _ (hfix t))]
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      have e1 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card =
          Nat.card {t : K // t * σ t = c * (h e e)⁻¹} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [eq_mul_inv_iff_mul_eq₀ he]
        constructor <;> intro H <;> linear_combination -H
      have hf : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
        rw [map_mul, map_inv₀, hc, hq.self_fixed]
      rw [e1, hN _ hf]
      by_cases hc0 : c = 0
      · simp [hc0]
      · have : c * (h e e)⁻¹ ≠ 0 := mul_ne_zero hc0 (inv_ne_zero he)
        simp [hc0, this]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hK, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hK, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul, hcnt]
    have e1 : (q : ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ (2 * (m : ℤ) - 1) * q ^ 2 := by
      rw [show 2 * ((m + 1 : ℕ) : ℤ) - 1 = (2 * m - 1) + 2 by push_cast; ring, zpow_add₀ hq']
      norm_cast
    have e2 : (q : ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ ((m : ℤ) - 1) * q := by
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 1 by push_cast; ring, zpow_add₀ hq',
        zpow_one]
    rw [e1, e2, pow_succ]
    by_cases hc0 : c = 0
    · simp only [hc0, if_true]; push_cast; ring
    · simp only [hc0, if_false]; push_cast; ring

theorem card_diag (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  intro a
  induction a with
  | zero =>
    intro m _ V _ _ _ h _ _ d _ _
    have : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨Fin.elim0, fun i => i.elim0⟩,
        fun y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [this]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hs hm d hd hd0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Fintype V := Fintype.ofFinite V
    classical
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ x : {x : V // h x x = d 0}, {Z : Fin a → perp hq x.1 //
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩,
          ⟨fun i => ⟨Y.1 i.succ, (mem_perp hq _ _).2 (by
            have := Y.2 0 i.succ; rwa [if_neg (Fin.succ_ne_zero i).symm] at this)⟩,
            fun i j => by
              have := Y.2 i.succ j.succ
              simpa only [Fin.succ_inj] using this⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero j).symm]
              exact (mem_perp hq _ _).1 (p.2.1 j).2
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hq.herm, (mem_perp hq _ _).1 (p.2.1 i).2,
                map_zero]
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_inj]
              exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (funext fun i => by
          induction i using Fin.cases with
          | zero => rfl
          | succ i => rfl)
        right_inv := fun p => rfl }
    rw [Nat.card_congr E, Nat.card_sigma, Nat.cast_sum]
    have hfr : ∀ x : {x : V // h x x = d 0}, finrank K (perp hq x.1) = m' := fun x => by
      have := finrank_perp hq x.1 (by rw [x.2]; exact hd0 0); omega
    have hsum : ∀ x : {x : V // h x x = d 0}, (Nat.card {Z : Fin a → perp hq x.1 //
        ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q : ℝ) ^ (m' - j - 1)) :=
      fun x => ih m' (by omega) (perp hq x.1) (fun w w' => h w w')
        (perp_isHS hs x.1 (by rw [x.2]; exact hd0 0)) (hfr x) (fun i => d i.succ)
        (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun x _ => hsum x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      card_norm q hq0 hK hσ h2 hN (m' + 1) V h hs hm (d 0) (hd 0), if_neg (hd0 0),
      Fin.prod_univ_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.sub_zero]
      rw [show 2 * ((m' + 1 : ℕ) : ℤ) - 1 = ((2 * (m' + 1) - 1 : ℕ) : ℤ) by omega,
        show ((m' + 1 : ℕ) : ℤ) - 1 = ((m' + 1 - 1 : ℕ) : ℤ) by omega, zpow_natCast,
        zpow_natCast]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fin.val_succ, show m' + 1 - (j + 1 : ℕ) = m' - j by omega]

end PI.VolStabW.FFHS
