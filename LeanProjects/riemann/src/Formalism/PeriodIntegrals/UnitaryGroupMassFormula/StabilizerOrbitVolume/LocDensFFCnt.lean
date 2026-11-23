import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  classical
  let T : V → K := fun x => (h e e)⁻¹ * h e x
  have hTe : ∀ (t : K) (w : perp hs e), T ((t • e) + (w : V)) = t := by
    intro t w
    simp only [T]
    rw [hs.add_right, hs.smul_right, (mem_perp hs e w).1 w.2, add_zero, ← mul_assoc,
      mul_comm ((h e e)⁻¹) t, mul_assoc, inv_mul_cancel₀ he, mul_one]
  let eqv : {x : V // h x x = c} ≃ Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨T x.1, ⟨⟨x.1 - T x.1 • e, perp_sub_mem hs e x.1 he⟩, by
        have h1 := decomp_val hs e (x.1 - T x.1 • e)
          ((mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)) (T x.1)
        have hx : T x.1 • e + (x.1 - T x.1 • e) = x.1 := by abel
        rw [hx, x.2] at h1
        show h (x.1 - T x.1 • e) (x.1 - T x.1 • e) = c - σ (T x.1) * T x.1 * h e e
        rw [eq_sub_iff_add_eq, add_comm]
        exact h1.symm⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
        rw [decomp_val hs e p.2.1 ((mem_perp hs e _).1 p.2.1.2) p.1]
        have h2 : h (p.2.1 : V) (p.2.1 : V) = c - σ p.1 * p.1 * h e e := p.2.2
        rw [h2]
        ring⟩
      left_inv := fun x => Subtype.ext (by
        show T x.1 • e + (x.1 - T x.1 • e) = x.1
        abel)
      right_inv := fun p => by
        refine Sigma.subtype_ext (hTe p.1 p.2.1) (Subtype.ext ?_)
        show p.1 • e + (p.2.1 : V) - T (p.1 • e + (p.2.1 : V)) • e = (p.2.1 : V)
        rw [hTe]
        abel }
  rw [Nat.card_congr eqv, Nat.card_sigma]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hh hm c hc
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hm
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hcard : Nat.card {x : V // h x x = c} = if c = 0 then 1 else 0 := by
      split_ifs with hc0
      · rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, by rw [hh.toIsSq.zero_left, hc0]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      · rw [Nat.card_eq_zero]
        left
        constructor
        intro x
        apply hc0
        rw [← x.2, Subsingleton.elim x.1 0, hh.toIsSq.zero_left]
    rw [hcard]
    split_ifs with hc0
    · push_cast
      field_simp
      ring
    · push_cast
      ring
  | succ m ih =>
    intro V _ _ _ h hh hm c hc
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    haveI : Finite V := Module.finite_of_finite K
    obtain ⟨x0, hx0⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x0 hx0
    have hdec := card_decomp hh.toIsSq e he c
    have haσ : σ (h e e) = h e e := hh.toIsSq.self_fixed e
    have hperp := perp_isHS hh e he
    have hfr : finrank K (perp hh.toIsSq e) = m := by
      have := finrank_perp hh.toIsSq e he
      omega
    have hterm : ∀ t : K, (Nat.card {w : perp hh.toIsSq e // h w w = c - σ t * t * h e e} : ℝ) =
        (q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1) := by
      intro t
      have hfix : σ (c - σ t * t * h e e) = c - σ t * t * h e e := by
        rw [map_sub, map_mul, map_mul, hσ, hc, haσ]
        ring
      exact ih (perp hh.toIsSq e) (fun w w' => h w w') hperp hfr _ hfix
    have hP : ∀ t : K, (c - σ t * t * h e e = 0) ↔ t * σ t = c / h e e := by
      intro t
      rw [sub_eq_zero, eq_div_iff he]
      exact ⟨fun h' => by rw [h']; ring, fun h' => by rw [← h']; ring⟩
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q:ℝ) + 1 := by
      have hfixd : σ (c / h e e) = c / h e e := by rw [map_div₀, hc, haσ]
      have h3 := hN (c / h e e) hfixd
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
      have h4 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)) =
          Finset.univ.filter (fun t => t * σ t = c / h e e) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hP t
      rw [h4, h3]
      have h5 : c / h e e = 0 ↔ c = 0 := div_eq_zero_iff.trans (or_iff_left he)
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, h5]
    have hsum : ∑ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
        (q:ℝ) * (q:ℝ) * ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
          (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (q:ℝ) *
            (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card := by
      have e1 : ∀ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
          ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
            (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (if c - σ t * t * h e e = 0 then (q:ℝ) else 0) :=
        fun t => by ring
      rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, hK, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [hdec, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t), hsum, hcnt]
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have e2 : (q:ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) * (q:ℝ) ^ (2 * (m:ℤ) - 1) := by
      rw [show (2 * ((m + 1 : ℕ) : ℤ) - 1) = 1 + 1 + (2 * (m:ℤ) - 1) by push_cast; ring,
        zpow_add₀ hr, zpow_add₀ hr, zpow_one]
    have e3 : (q:ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) ^ ((m:ℤ) - 1) := by
      rw [show (((m + 1 : ℕ) : ℤ) - 1) = 1 + ((m:ℤ) - 1) by push_cast; ring, zpow_add₀ hr, zpow_one]
    rw [e2, e3, pow_succ]
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
    intro m _ V _ _ _ h hh hm d hd hd0
    rw [Fin.prod_univ_zero]
    have h1 : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2
        ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun Y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    rw [h1]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hh hm d hd hd0
    classical
    haveI : Finite V := Module.finite_of_finite K
    haveI := Fintype.ofFinite V
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    let eqv : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y0 : {x : V // h x x = d 0}, {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩, ⟨fun i => ⟨Y.1 i.succ, by
            rw [mem_perp]
            have h3 := Y.2 0 i.succ
            rwa [if_neg (Fin.succ_ne_zero i).symm] at h3⟩,
          fun i j => by
            have h3 := Y.2 i.succ j.succ
            simpa [Fin.succ_inj] using h3⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · simpa using p.1.2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero j).symm]
            exact (mem_perp _ _ _).1 (p.2.1 j).2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero i), hh.toIsSq.herm p.1.1 (p.2.1 i),
              (mem_perp _ _ _).1 (p.2.1 i).2, map_zero]
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := fun p => rfl }
    rw [Nat.card_congr eqv, Nat.card_sigma, Nat.cast_sum]
    have hfib : ∀ y0 : {x : V // h x x = d 0}, (Nat.card {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      intro y0
      have hy0 : h y0.1 y0.1 ≠ 0 := by rw [y0.2]; exact hd0 0
      have hfr : finrank K (perp hh.toIsSq y0.1) = m' := by
        have := finrank_perp hh.toIsSq y0.1 hy0
        omega
      exact ih m' (by omega) (perp hh.toIsSq y0.1) (fun w w' => h w w') (perp_isHS hh y0.1 hy0) hfr
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun y0 _ => hfib y0), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN0 := card_norm q hq0 hK hσ h2 hN (m' + 1) V h hh hm (d 0) (hd 0)
    rw [← Nat.card_eq_fintype_card, hN0, if_neg (hd0 0), Fin.prod_univ_succ]
    have z1 : (q:ℝ) ^ (2 * ((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (2 * (m' + 1 - ((0 : Fin (a + 1)) : ℕ)) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    have z2 : (q:ℝ) ^ (((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (m' + 1 - ((0 : Fin (a + 1)) : ℕ) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    rw [z1, z2]
    have hP : ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' + 1 - (j.succ : ℕ)) - 1) -
        (-1) ^ (m' + 1 - (j.succ : ℕ)) * (q:ℝ) ^ (m' + 1 - (j.succ : ℕ) - 1)) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fin.val_succ, Nat.add_sub_add_right]
    rw [hP]
    simp only [Fin.val_zero, Nat.sub_zero]
    ring

end PI.VolStabSW.FFHS
