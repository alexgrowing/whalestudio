import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_hcParam_of_code (R : Ranks) (D h : ℕ) (hD : 1 ≤ D) (hh : ((R.t : ℚ) + 3) / 2 ≤ h)
    (U0 UL B : ℤ) (h0 : ((R.k - 2 : ℕ) : ℚ) * (4 * (D : ℚ)) ≤ U0) (hL : UL < 0) (hB : -B ≤ UL)
    (w : Fin (R.k - 2) → Bool) :
    ∃ p : HCParam R, (∀ i : Fin (R.k - 1), p.v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ))) ∧
      (∀ hk : 0 < R.k, p.u ⟨0, hk⟩ = U0 + 1 / 2 ∧ p.u ⟨R.k - 1, by omega⟩ = UL + 1 / 2) ∧
      (∀ (l : ℕ) (hl : l < R.k - 2), p.u ⟨l + 1, by omega⟩ =
        ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0)) ∧
      ∀ j : Fin R.m, p.b j = B + (j.1 : ℚ) * (2 * h) ∧ p.e j = p.b j + h := by
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  have hD' : (1 : ℚ) ≤ D := by exact_mod_cast hD
  let u : Fin R.k → ℚ := fun i =>
    if i.1 = 0 then U0 + 1 / 2 else
      if hi : i.1 - 1 < R.k - 2 then
        ((R.k - 2 - (i.1 - 1) : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨i.1 - 1, hi⟩ then (D : ℚ) else 0)
      else UL + 1 / 2
  have u0 : ∀ hk : 0 < R.k, u ⟨0, hk⟩ = U0 + 1 / 2 := fun hk => by simp [u]
  have uL : ∀ hk : R.k - 1 < R.k, u ⟨R.k - 1, hk⟩ = UL + 1 / 2 := fun hk => by
    have h1 : ¬ (R.k - 1 = 0) := by omega
    have h2 : ¬ (R.k - 1 - 1 < R.k - 2) := by omega
    simp only [u, h1, h2, if_false, dite_false]
  have um : ∀ (l : ℕ) (hl : l < R.k - 2) (hk : l + 1 < R.k), u ⟨l + 1, hk⟩ =
      ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0) := fun l hl hk => by
    simp only [u, Nat.add_one_ne_zero, Nat.add_sub_cancel, hl, if_false, dite_true]
  have hLq : (UL : ℚ) ≤ -1 := by exact_mod_cast (by omega : UL ≤ -1)
  have hBq : -(B : ℚ) ≤ UL := by exact_mod_cast hB
  refine ⟨⟨u, fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ)), fun j => B + (j.1 : ℚ) * (2 * h),
    fun j => B + (j.1 : ℚ) * (2 * h) + h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun i => rfl, fun hk => ⟨u0 hk, uL _⟩, fun l hl => um l hl _, fun j => ⟨rfl, rfl⟩⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · rw [u0]; simp only [Nat.sub_zero]; linarith
    · have hl : l < R.k - 2 := by omega
      rw [um l hl]
      have : R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 := by omega
      rw [this]; push_cast
      split_ifs <;> linarith
  · rintro ⟨l, hi⟩
    by_cases hl : l < R.k - 2
    · rw [um l hl]
      split_ifs <;> linarith
    · have e1 : l + 1 = R.k - 1 := by omega
      have e2 : R.k - 2 - l = 0 := by omega
      have : u ⟨l + 1, by omega⟩ = UL + 1 / 2 := by
        rw [← uL (by omega)]; congr 2
      simp only [this, e2]
      push_cast; linarith
  · intro hk hm
    rw [uL]; simp only [Nat.cast_zero]; linarith
  · intro j; linarith
  · intro j hj; push_cast; linarith
  · intro j; exact ⟨B + j.1 * (2 * h) + h, by push_cast; ring⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · exact ⟨U0, u0 _⟩
    · by_cases hl : l < R.k - 2
      · rw [um l hl]
        split_ifs
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1 - D, by push_cast; ring⟩
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1, by push_cast; ring⟩
      · have e1 : l + 1 = R.k - 1 := by omega
        refine ⟨UL, ?_⟩
        rw [← uL (by omega)]; congr 2
  · intro i; exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * D), by push_cast; ring⟩
  · intro j; exact ⟨B + j.1 * (2 * h), by push_cast; ring⟩

theorem hc_sizes (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      1 ≤ Delv s cD ∧ ((R.t : ℚ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) ∧
      (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.a ∧ (R.k : ℝ) ≤ s.b' / s.x ∧ 0 < s.b' ∧ 0 < s.b ∧ 0 < s.w'' R.n := by
  obtain ⟨x1, H1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) 1 h0 one_pos
  obtain ⟨x2, H2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  have hx8 : 8 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hS, -⟩ := H1 s he hx1
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, ht, -⟩ := H2 s R he hx2 hR
  have hxp : 0 < s.x := by linarith
  have hx1' : 1 ≤ s.x := by linarith
  rw [Real.rpow_one] at hS
  have hb : 0 < s.b := Real.exp_pos _
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  have hXp : 0 < s.X' := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hD1 : 1 ≤ s.x ^ cD := Real.one_le_rpow hx1' hcD
  have h5 : 1 ≤ s.x ^ (5 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
  have hsplit : s.x ^ (cD + 6) = s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by
    rw [show cD + 6 = cD + 5 + 1 by ring, Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_one]
  have hDle : (Delv s cD : ℝ) ≤ 2 * s.x ^ cD := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ cD by linarith)
    unfold Delv; linarith
  have hb' : 0 < s.b' := div_pos (mul_pos hxp hb) hXp
  have hn : (0 : ℝ) < R.n := by unfold Ranks.n; positivity
  refine ⟨?_, ?_, ?_, ?_, hb', hb, div_pos hb' (mul_pos hxp hn)⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  · have h401 : 1 ≤ s.x ^ (401 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
    have h402 : s.x ^ (401 : ℝ) * s.x ≤ s.x ^ ch := by
      rw [← Real.rpow_add_one hxp.ne']
      exact Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
    have hc := Nat.le_ceil (s.x ^ ch)
    have : ((R.t : ℝ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) := by nlinarith
    have h' : ((((R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((⌈s.x ^ ch⌉₊ : ℕ) : ℚ) : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  · have hP : 0 ≤ s.x ^ cD * s.x ^ (5 : ℝ) := by positivity
    have e1 : (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.x ^ (5 : ℝ) * (4 * (2 * s.x ^ cD)) := by gcongr
    have e2 : s.x ^ (cD + 6) ≤ s.x ^ (cD + 6) * s.X' := le_mul_of_one_le_right (by positivity) hX
    have e3 : s.b ≤ s.a := le_mul_of_one_le_left hb.le hx1'
    have e4 : s.x ^ cD * s.x ^ (5 : ℝ) * 8 ≤ s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by gcongr
    linarith
  · have e : s.b' / s.x = s.b / s.X' := by
      unfold Scale.b' Scale.a; field_simp
    rw [e, le_div_iff₀ hXp]
    refine le_trans ?_ hS
    gcongr
    exact le_trans hk (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))

theorem exists_hc_family : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (aT bT : H.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → (∀ t, s.a ≤ (aT t : ℝ) ∧ s.b' ≤ (bT t : ℝ)) → ∀ (Tau : Type) [Fintype Tau] (eTau : Tau ≃ R.Psi), ∃ hcw : (Fin (R.k - 2) → Bool) → Tau → HCParam R, (∀ w, HCVal s cD ch H (fun τ => (eTau τ : R.GG)) (hcw w) bT) ∧ (∀ w w' τ, (hcw w τ).v = (hcw w' τ).v ∧ (hcw w τ).b = (hcw w' τ).b ∧ (hcw w τ).e = (hcw w' τ).e ∧ ∀ h : 0 < R.k, (hcw w τ).u ⟨0, h⟩ = (hcw w' τ).u ⟨0, h⟩ ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = (hcw w' τ).u ⟨R.k - 1, by omega⟩) ∧ (∀ w τ (l : ℕ) (h : l < R.k - 2), (hcw w τ).u ⟨l + 1, by omega⟩ = (hcw w τ).v ⟨l, by omega⟩ - 1 / 2 - (if w ⟨l, h⟩ then (Delv s cD : ℚ) else 0)) ∧ ∀ w τ (t : H.TT) (h : 0 < R.k), (eTau τ : R.GG) = R.tau1 t → (hcw w τ).u ⟨0, h⟩ = (aT t : ℚ) + ((R.k : ℚ) - 1) / 2 ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = -(bT t : ℚ) - ((R.k : ℚ) - 1) / 2 := by
  intro eps cD ch C8 he0 he1 hcD hch
  obtain ⟨x0, Hs⟩ := hc_sizes eps cD ch he0 he1 hcD hch
  refine ⟨x0, fun s R H aT bT he hx hR hH hab Tau _ eTau => ?_⟩
  classical
  obtain ⟨hD, hh, hka, hkb, hb', hb, hw⟩ := Hs s R he hx hR
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  obtain ⟨κ, hκ⟩ := R.k_even
  have hκq : (R.k : ℚ) = 2 * κ := by rw [hκ]; push_cast; ring
  obtain ⟨-, hthP, hdisj, -, hcard⟩ := factTopsThick R H
  have hinj : ∀ t t' : H.TT, R.tau1 t = R.tau1 t' → t = t' := fun t t' h =>
    Subtype.ext (R.iota_bijective.1 (congrArg Prod.snd h))
  have htop : ∀ g, g ∈ H.topPlaces ↔ ∃ t : H.TT, g = R.tau1 t := fun g => by
    unfold Host.topPlaces
    rw [Finset.mem_image]
    exact ⟨fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e.symm⟩, fun ⟨t, e⟩ => ⟨t.1, t.2, e.symm⟩⟩
  have hne : H.thickPlaces.Nonempty := by
    rw [← Finset.card_pos, hcard]
    have h1 := hH.2.2.1
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have hn : (0 : ℝ) < R.n := by unfold Ranks.n; positivity
    have : (0 : ℝ) < H.T2.card := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hxp _) hn) h1
    exact_mod_cast this
  obtain ⟨g0, hg0⟩ := hne
  let τ0 : Tau := eTau.symm ⟨g0, hthP g0 hg0⟩
  have hτ0 : (eTau τ0 : R.GG) = g0 := by simp [τ0]
  let base : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then bT h.choose + ⌊s.b' / s.x⌋
    else if (eTau τ : R.GG) ∈ H.thickPlaces then ⌈s.b⌉ else ⌈s.w'' R.n⌉
  obtain ⟨sh, hsh, hMU⟩ := UpperTheory.Mu.exists_shift H eTau base τ0
  let ε : ℤ := (sh : ℤ)
  have hε : 0 ≤ ε ∧ ε < (NumberField.Units.torsionOrder H.E : ℤ) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 hsh⟩
  let b1 : Tau → ℤ := fun τ => base τ + if τ = τ0 then ε else 0
  let U0 : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then aT h.choose + κ - 1
    else ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD)
  let UL : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then -bT h.choose - κ else -1
  have hT : ∀ τ (t : H.TT), (eTau τ : R.GG) = R.tau1 t →
      b1 τ = bT t + ⌊s.b' / s.x⌋ ∧ U0 τ = aT t + κ - 1 ∧ UL τ = -bT t - κ := fun τ t ht => by
    have h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := ⟨t, ht⟩
    have hc : h.choose = t := hinj _ _ (h.choose_spec.symm.trans ht)
    have hτ : τ ≠ τ0 := by
      rintro rfl
      exact Finset.disjoint_left.1 hdisj ((htop _).2 h) (hτ0 ▸ hg0)
    simp only [b1, base, U0, UL, dif_pos h, hc, if_neg hτ, add_zero, and_self]
  have hN : ∀ τ, (¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t) →
      1 ≤ b1 τ ∧ U0 τ = ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD) ∧ UL τ = -1 := fun τ h => by
    have c1 : 0 < ⌈s.b⌉ := Int.ceil_pos.2 hb
    have c2 : 0 < ⌈s.w'' R.n⌉ := Int.ceil_pos.2 hw
    simp only [b1, base, U0, UL, dif_neg h, and_self, and_true]
    split_ifs <;> omega
  have hcond : ∀ τ, ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) ≤ U0 τ ∧ UL τ < 0 ∧ -b1 τ ≤ UL τ := fun τ => by
    by_cases h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨e1, e2, e3⟩ := hT τ t ht
      have a1 : (R.k : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t := by
        have := hka.trans (hab t).1
        exact_mod_cast this
      have a2 : 0 < bT t := by
        have := hb'.trans_le (hab t).2
        exact_mod_cast this
      have a3 : (R.k : ℤ) ≤ ⌊s.b' / s.x⌋ := Int.le_floor.2 (by exact_mod_cast hkb)
      rw [e1, e2, e3]
      refine ⟨?_, by omega, by omega⟩
      have a4 : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ (R.k : ℤ) * (4 * (Delv s cD : ℤ)) := by
        gcongr; omega
      have : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t + κ - 1 := by omega
      exact_mod_cast this
    · obtain ⟨e1, e2, e3⟩ := hN τ h
      rw [e2, e3]
      refine ⟨?_, by omega, by omega⟩
      push_cast
      have : (0 : ℚ) ≤ (R.k : ℚ) * (4 * (Delv s cD : ℚ)) := by positivity
      linarith
  choose p hv hu hm hbe using fun (w : Fin (R.k - 2) → Bool) (τ : Tau) =>
    exists_hcParam_of_code R (Delv s cD) ⌈s.x ^ ch⌉₊ hD hh (U0 τ) (UL τ) (b1 τ)
      (hcond τ).1 (hcond τ).2.1 (hcond τ).2.2 w
  have hh0 : (h0v s ch : ℚ) = 2 * (⌈s.x ^ ch⌉₊ : ℕ) := by unfold h0v; push_cast; ring
  refine ⟨p, fun w => ⟨fun τ i => hv w τ i, fun τ hk hτ => ?_, ⟨b1, fun τ j => ?_, fun τ t ht => (hT τ t ht).1,
    fun τ hτ => ?_, fun τ hτ => ?_⟩, fun j => ?_⟩, fun w w' τ => ⟨?_, ?_, ?_, fun h => ?_⟩, fun w τ l h => ?_,
    fun w τ t h ht => ?_⟩
  · obtain ⟨-, e2, e3⟩ := hN τ (fun h => hτ ((htop _).2 h))
    rw [(hu w τ hk).1, (hu w τ hk).2, e2, e3]
    constructor
    · push_cast; ring
    · norm_num
  · rw [(hbe w τ j).2, (hbe w τ j).1, hh0]
    constructor <;> ring
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h =>
      Finset.disjoint_left.1 hdisj ((htop _).2 h) hτ
    have hτ' : (eTau τ : R.GG) ∈ H.thickPlaces := hτ
    simp only [b1, base, dif_neg h, if_pos hτ']
    split_ifs <;> omega
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h => hτ.2.1 ((htop _).2 h)
    have hτ' : (eTau τ : R.GG) ∉ H.thickPlaces := hτ.2.2
    have hτ1 : τ ≠ τ0 := by
      rintro rfl
      exact hτ' (hτ0 ▸ hg0)
    simp only [b1, base, dif_neg h, if_neg hτ', if_neg hτ1, add_zero]
  · refine UpperTheory.Mu.muq_of_parallel H eTau hMU (j.1 * (2 * (⌈s.x ^ ch⌉₊ : ℕ)) + (⌈s.x ^ ch⌉₊ : ℕ)) (fun τ => ?_)
    rw [(hbe w τ j).2, (hbe w τ j).1]
    change _ = ((b1 τ : ℤ) : ℚ) + _
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    ring
  · funext i; rw [hv, hv]
  · funext j; rw [(hbe w τ j).1, (hbe w' τ j).1]
  · funext j; rw [(hbe w τ j).2, (hbe w' τ j).2, (hbe w τ j).1, (hbe w' τ j).1]
  · rw [(hu w τ h).1, (hu w τ h).2, (hu w' τ h).1, (hu w' τ h).2]; exact ⟨rfl, rfl⟩
  · rw [hm w τ l h, hv]
  · obtain ⟨-, e2, e3⟩ := hT τ t ht
    rw [(hu w τ h).1, (hu w τ h).2, e2, e3, hκq]
    constructor <;> (push_cast; ring)

end GlobalTheory.EX
