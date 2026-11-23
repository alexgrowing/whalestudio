import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFHS

noncomputable section

namespace PI.VolStabS.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right]
  rw [mul_comm (h e e)⁻¹ (h e x), mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]

private theorem natCard_sigma_eq_sum {α : Type} [Fintype α] {β : α → Type} [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  exact Nat.card_sigma

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  have hcoef : ∀ (t : K) (w : V), h e w = 0 → (h e e)⁻¹ * h e (t • e + w) = t := by
    intro t w hw
    rw [hs.add_right, hs.smul_right, hw, add_zero]
    rw [mul_comm t, ← mul_assoc, inv_mul_cancel₀ he, one_mul]
  let E : {x : V // h x x = c} ≃
      Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨(h e e)⁻¹ * h e x.1,
        ⟨⟨x.1 - ((h e e)⁻¹ * h e x.1) • e, perp_sub_mem hs e x.1 he⟩, by
          have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
          have key := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
          have hx : ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1 := by
            abel
          rw [hx, x.2] at key
          show h (x.1 - ((h e e)⁻¹ * h e x.1) • e) (x.1 - ((h e e)⁻¹ * h e x.1) • e) = _
          linear_combination -key⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
          rw [decomp_val hs e _ ((mem_perp hs e _).1 p.2.1.2) p.1, p.2.2]
          ring⟩
      left_inv := fun x => Subtype.ext (by
          show ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1
          abel)
      right_inv := by
        rintro ⟨t, ⟨w, hw⟩, hww⟩
        have hw0 := (mem_perp hs e w).1 hw
        refine Sigma.subtype_ext (hcoef t w hw0) ?_
        apply Subtype.ext
        show t • e + w - ((h e e)⁻¹ * h e (t • e + w)) • e = w
        rw [hcoef t w hw0]
        abel }
  rw [Nat.card_congr E, natCard_sigma_eq_sum]

private theorem natCard_subtype_eq_card_filter {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] : Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hQ : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
  have z1 : ∀ n : ℕ, (q : ℝ) ^ (2 * (n : ℤ) - 1) = (q : ℝ) ^ (2 * n) * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv,
      show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by omega, zpow_natCast]
  have z2 : ∀ n : ℕ, (q : ℝ) ^ ((n : ℤ) - 1) = (q : ℝ) ^ n * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv, zpow_natCast]
  intro m
  induction m with
  | zero =>
    intro V i1 i2 i3 h hh hm c hc
    have : Subsingleton V := by
      rcases subsingleton_or_nontrivial V with hV | hV
      · exact hV
      · exfalso
        have hpos : 0 < finrank K V := Module.finrank_pos
        omega
    have h00 : h 0 0 = 0 := hh.toIsSq.zero_left 0
    simp only [z1, z2]
    by_cases hc0 : c = 0
    · subst hc0
      have hcard : Nat.card {x : V // h x x = 0} = 1 := by
        have : Unique {x : V // h x x = 0} :=
          ⟨⟨⟨0, h00⟩⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
        exact Nat.card_unique
      rw [hcard, if_pos rfl, Nat.cast_one]
      have hqq : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hQ
      linear_combination -hqq
    · have hcard : Nat.card {x : V // h x x = c} = 0 := by
        have : IsEmpty {x : V // h x x = c} :=
          ⟨fun y => hc0 (by
            have hy := y.2
            rw [Subsingleton.elim y.1 0, h00] at hy
            exact hy.symm)⟩
        exact Nat.card_of_isEmpty
      rw [hcard, if_neg hc0, Nat.cast_zero]
      ring
  | succ m ih =>
    intro V i1 i2 i3 h hh hm c hc
    have hs := hh.toIsSq
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x hx
    have hW := perp_isHS hh e he
    have hWr : finrank K (perp hs e) = m := by
      have := finrank_perp hs e he
      omega
    have : Finite V := Module.finite_of_finite K
    have hterm : ∀ t : K, (Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} : ℝ) =
        (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1) := by
      intro t
      refine ih (perp hs e) (fun w w' : perp hs e => h w w') hW hWr _ ?_
      simp only [map_sub, map_mul, hσ, hc, hs.self_fixed]
      ring
    have hfix : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
      rw [map_mul, map_inv₀, hc, hs.self_fixed]
    have hiff : ∀ t : K, c - σ t * t * h e e = 0 ↔ t * σ t = c * (h e e)⁻¹ := by
      intro t
      constructor
      · intro H
        have H' : σ t * t * h e e = c := (sub_eq_zero.1 H).symm
        rw [← H', mul_inv_cancel_right₀ he, mul_comm]
      · intro H
        rw [mul_comm (σ t) t, H, mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]
    have hcount : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      rw [← natCard_subtype_eq_card_filter, Nat.card_congr (Equiv.subtypeEquivRight hiff),
        hN _ hfix]
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, he]
    have hsum : ∑ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
        (q : ℝ) ^ 2 * ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
          (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
            ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) := by
      have hpt : ∀ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
          ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
            (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
              (if c - σ t * t * h e e = 0 then (1 : ℝ) else 0) := by
        intro t
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_boole, Finset.sum_const, Finset.card_univ, hK, nsmul_eq_mul, Nat.cast_pow]
    rw [card_decomp hs e he c, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t),
      hsum, hcount]
    simp only [z1, z2]
    split_ifs <;> ring

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
    intro m _ V i1 i2 i3 h _ _ d _ _
    have : Unique {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} :=
      ⟨⟨⟨Fin.elim0, fun i => i.elim0⟩⟩, fun Y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [Nat.card_unique, Fin.prod_univ_zero, Nat.cast_one]
  | succ a ih =>
    intro m ham V i1 i2 i3 h hh hm d hd hd0
    have hs := hh.toIsSq
    have : Finite V := Module.finite_of_finite K
    letI : Fintype V := Fintype.ofFinite V
    have hfibEq : ∀ y : V, Nat.card {Z : Fin a → V // (∀ i, h y (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} =
        Nat.card {W : Fin a → perp hs y //
          ∀ i j, h (W i) (W j) = if i = j then d i.succ else 0} := by
      intro y
      apply Nat.card_congr
      exact
        { toFun := fun Z => ⟨fun i => ⟨Z.1 i, (mem_perp hs y _).2 (Z.2.1 i)⟩, Z.2.2⟩
          invFun := fun W => ⟨fun i => (W.1 i : V),
            fun i => (mem_perp hs y _).1 (W.1 i).2, W.2⟩
          left_inv := fun Z => rfl
          right_inv := fun W => rfl }
    have hfib : ∀ y : {y : V // h y y = d 0},
        (Nat.card {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
          ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - 1 - j) - 1) -
            (-1) ^ (m - 1 - j) * (q : ℝ) ^ (m - 1 - j - 1)) := by
      intro y
      have hy0 : h y.1 y.1 ≠ 0 := by rw [y.2]; exact hd0 0
      rw [hfibEq y.1]
      exact ih (m - 1) (by omega) (perp hs y.1) (fun w w' : perp hs y.1 => h w w')
        (perp_isHS hh y.1 hy0)
        (by have := finrank_perp hs y.1 hy0; omega)
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y : {y : V // h y y = d 0}, {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, (Y.2 0 0).trans (if_pos rfl)⟩,
          ⟨fun i => Y.1 i.succ, fun i => (Y.2 0 i.succ).trans (if_neg (Fin.succ_ne_zero i).symm),
            fun i j => (Y.2 i.succ j.succ).trans (by simp only [Fin.succ_inj])⟩⟩
        invFun := fun p => ⟨(Fin.cons p.1.1 p.2.1 : Fin (a + 1) → V), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j => simpa [(Fin.succ_ne_zero j).symm] using p.2.2.1 j
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hs.herm, p.2.2.1 i, map_zero]
            | succ j => simpa [Fin.succ_inj] using p.2.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := by
          rintro ⟨⟨y, hy⟩, ⟨Z, hZ⟩⟩
          refine Sigma.subtype_ext (Subtype.ext (by simp)) ?_
          funext i
          simp }
    have hN0 : (Nat.card {y : V // h y y = d 0} : ℝ) =
        (q : ℝ) ^ (2 * m - 1) - (-1) ^ m * (q : ℝ) ^ (m - 1) := by
      rw [card_norm q hq0 hK hσ h2 hN m V h hh hm (d 0) (hd 0), if_neg (hd0 0),
        show (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) by omega,
        show ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast, zpow_natCast]
      ring
    have hsub : ∀ j : ℕ, m - (j + 1) = m - 1 - j := fun j => by omega
    rw [Nat.card_congr E, natCard_sigma_eq_sum, Nat.cast_sum,
      Finset.sum_congr rfl (fun y _ => hfib y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hN0, Fin.prod_univ_succ]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl (fun j _ => ?_)
         simp only [Fin.val_succ, hsub j])
      | simp only [Fin.val_zero, Nat.sub_zero]
      | rfl

end PI.VolStabS.FFHS
