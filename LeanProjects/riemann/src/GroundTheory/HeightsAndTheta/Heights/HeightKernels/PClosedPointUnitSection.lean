import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointUnitSection
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain

noncomputable section

namespace ClosedPointUnitSectionAlt

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

theorem mem_chartLat_iff {d : ℕ} {g : K'} :
    g ∈ chartLat y 1 d ↔
      ∀ t : T, y ⟨(), t⟩ ≠ 0 → g / y ⟨(), t⟩ ^ d ∈ chartRingZ y (fun _ => t) := by
  have key : ∀ c : Unit → T, c = fun _ => c () := fun c => funext fun u => by cases u; rfl
  show (∀ c : Unit → T, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      g * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y c) ↔ _
  constructor
  · intro h t ht
    have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv, zpow_neg, zpow_natCast] using this
  · intro h c hc
    have := h (c ()) (hc ())
    rw [key c]
    simpa [div_eq_mul_inv, zpow_neg, zpow_natCast] using this

omit [Fintype T] in

theorem coord_mem (u : T) : y ⟨(), u⟩ ∈ chartLat y 1 1 := by
  rw [mem_chartLat_iff]
  intro t _
  rw [pow_one]
  exact Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩

omit [Fintype T] in

theorem chartLat_mul_mem {a b : ℕ} {g h : K'} (hg : g ∈ chartLat y 1 a) (hh : h ∈ chartLat y 1 b) :
    g * h ∈ chartLat y 1 (a + b) := by
  rw [mem_chartLat_iff] at hg hh ⊢
  intro t ht
  rw [pow_add, mul_div_mul_comm]
  exact Subalgebra.mul_mem _ (hg t ht) (hh t ht)

omit [Fintype T] in
theorem chartLat_pow_mem {a : ℕ} {g : K'} (hg : g ∈ chartLat y 1 a) (n : ℕ) :
    g ^ n ∈ chartLat y 1 (a * n) := by
  induction n with
  | zero =>
    rw [mem_chartLat_iff]
    intro t _
    simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact chartLat_mul_mem y ih hg

omit [Fintype T] in

theorem exists_mul_pow_mem_chartLat (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ chartRingZ y (fun _ => t)) : ∃ k : ℕ, x * y ⟨(), t⟩ ^ k ∈ chartLat y 1 k := by
  have hpow : ∀ l : ℕ, y ⟨(), t⟩ ^ l ∈ chartLat y 1 l := fun l => by
    simpa only [one_mul] using chartLat_pow_mem y (coord_mem y t) l
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    refine ⟨1, ?_⟩
    show y ⟨(), u⟩ / y ⟨(), t⟩ * y ⟨(), t⟩ ^ 1 ∈ chartLat y 1 1
    rw [pow_one, div_mul_cancel₀ _ ht]
    exact coord_mem y u
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [mem_chartLat_iff]
    intro s _
    simp
  | add x z _ _ hx hz =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    have e : (x + z) * y ⟨(), t⟩ ^ (k + l) =
        x * y ⟨(), t⟩ ^ k * y ⟨(), t⟩ ^ l + z * y ⟨(), t⟩ ^ l * y ⟨(), t⟩ ^ k := by ring
    rw [e]
    have h2 := chartLat_mul_mem y hl (hpow k)
    rw [Nat.add_comm] at h2
    exact add_mem (chartLat_mul_mem y hk (hpow l)) h2
  | mul x z _ _ hx hz =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    have e : x * z * y ⟨(), t⟩ ^ (k + l) = (x * y ⟨(), t⟩ ^ k) * (z * y ⟨(), t⟩ ^ l) := by ring
    rw [e]
    exact chartLat_mul_mem y hk hl

variable [NumberField K']

def IsUnitAt (P : HeightOneSpectrum (𝓞 K')) (d : ℕ) (g : K') : Prop :=
  ∀ u : T, P.valuation K' (y ⟨(), u⟩) ^ d ≤ P.valuation K' g

theorem exists_max (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K')) :
    ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧ ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩) := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => P.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  refine ⟨t, fun h0 => ht0 ?_, fun u => ht u (Finset.mem_univ _)⟩
  have h1 := ht t0 (Finset.mem_univ _)
  rw [h0, map_zero] at h1
  exact (Valuation.zero_iff _).mp (le_antisymm h1 zero_le)

omit [Fintype T] in

theorem le_of_mem {P : HeightOneSpectrum (𝓞 K')} {t : T} (ht0 : y ⟨(), t⟩ ≠ 0)
    (ht : ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩)) {d : ℕ} {g : K'}
    (hg : g ∈ chartLat y 1 d) : P.valuation K' g ≤ P.valuation K' (y ⟨(), t⟩) ^ d := by
  have h1 := CurveAffineCharts.mem_integer_of_mem_chartRingZ y P t ht ((mem_chartLat_iff y).mp hg t ht0)
  rw [Valuation.mem_integer_iff, map_div₀, map_pow] at h1
  have hpos : P.valuation K' (y ⟨(), t⟩) ^ d ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0)
  exact (div_le_one₀ (zero_lt_iff.mpr hpos)).mp h1

omit [Fintype T] in
theorem isUnitAt_iff {P : HeightOneSpectrum (𝓞 K')} {t : T}
    (ht : ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩)) {d : ℕ} {g : K'} :
    IsUnitAt y P d g ↔ P.valuation K' (y ⟨(), t⟩) ^ d ≤ P.valuation K' g :=
  ⟨fun h => h t, fun h u => (pow_le_pow_left' (ht u) d).trans h⟩

omit [Fintype T] in
theorem IsUnitAt.mul {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ} {g h : K'} (hg : IsUnitAt y P a g)
    (hh : IsUnitAt y P b h) : IsUnitAt y P (a + b) (g * h) := fun u => by
  rw [pow_add, map_mul]
  exact mul_le_mul' (hg u) (hh u)

omit [Fintype T] in
theorem IsUnitAt.pow {P : HeightOneSpectrum (𝓞 K')} {a : ℕ} {g : K'} (hg : IsUnitAt y P a g) (n : ℕ) :
    IsUnitAt y P (a * n) (g ^ n) := fun u => by
  rw [pow_mul, map_pow]
  exact pow_le_pow_left' (hg u) n

theorem not_isUnitAt_mul (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ}
    {g h : K'} (hg : ¬IsUnitAt y P a g) (hh : h ∈ chartLat y 1 b) : ¬IsUnitAt y P (a + b) (g * h) := by
  obtain ⟨t, ht0, ht⟩ := exists_max y hy P
  rw [isUnitAt_iff y ht, not_le] at hg ⊢
  rw [map_mul, pow_add]
  have hb := le_of_mem y ht0 ht hh
  have hpos : 0 < P.valuation K' (y ⟨(), t⟩) ^ b :=
    zero_lt_iff.mpr (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0))
  calc P.valuation K' g * P.valuation K' h ≤ P.valuation K' g * P.valuation K' (y ⟨(), t⟩) ^ b :=
        mul_le_mul' le_rfl hb
    _ < P.valuation K' (y ⟨(), t⟩) ^ a * P.valuation K' (y ⟨(), t⟩) ^ b :=
        mul_lt_mul_of_pos_right hg hpos

theorem not_isUnitAt_pow (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {a : ℕ}
    {g : K'} (hg : ¬IsUnitAt y P a g) (hga : g ∈ chartLat y 1 a) (n : ℕ) :
    ¬IsUnitAt y P (a * (n + 1)) (g ^ (n + 1)) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    have := not_isUnitAt_mul y hy ih hga
    rw [← pow_succ] at this
    convert this using 2
    ring

theorem isUnitAt_add (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {g h : K'} (hg : IsUnitAt y P d g) (hh : ¬IsUnitAt y P d h) : IsUnitAt y P d (g + h) := by
  obtain ⟨t, -, ht⟩ := exists_max y hy P
  rw [isUnitAt_iff y ht] at hg hh ⊢
  rw [not_le] at hh
  rwa [Valuation.map_add_eq_of_lt_left _ (hh.trans_le hg)]

omit [Fintype T] in

theorem exists_pow_sub_one (P : HeightOneSpectrum (𝓞 K')) {x : K'} (hx : P.valuation K' x = 1) :
    ∃ N : ℕ, 1 ≤ N ∧ P.valuation K' (x ^ N - 1) < 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P x hx.le
  have hd : (d : 𝓞 K') ∉ P.asIdeal := d.2
  have hd1 : P.valuation K' (algebraMap (𝓞 K') K' d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hd
  have hn : (n : 𝓞 K') ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K'), ← hnd, map_mul, hx, one_mul]
    exact hd1
  have hdK : algebraMap (𝓞 K') K' d ≠ 0 := fun h => by
    rw [h, map_zero] at hd1
    exact zero_ne_one hd1
  have := P.isMaximal
  let _ : Field (𝓞 K' ⧸ P.asIdeal) := Ideal.Quotient.field _
  let _ : Fintype (𝓞 K' ⧸ P.asIdeal) := Fintype.ofFinite _
  have hq : 1 < Fintype.card (𝓞 K' ⧸ P.asIdeal) := Fintype.one_lt_card
  have hmk : ∀ a : 𝓞 K', a ∉ P.asIdeal →
      Ideal.Quotient.mk P.asIdeal a ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) = 1 := fun a ha =>
    FiniteField.pow_card_sub_one_eq_one _ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hmem : (n : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) -
      (d : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, hmk _ hn, hmk _ hd, sub_self]
  refine ⟨Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1, by omega, ?_⟩
  have e : x ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) - 1 =
      algebraMap (𝓞 K') K' ((n : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) -
        (d : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1)) /
        algebraMap (𝓞 K') K' d ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) := by
    rw [eq_div_iff (pow_ne_zero _ hdK), map_sub, map_pow, map_pow, ← hnd]
    ring
  rw [e, map_div₀, map_pow, hd1, one_pow, div_one]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr hmem

theorem exists_sep (hy : IsArithVar (mCoordIdeal y) 1) {P P' : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {G : K'} (hG : G ∈ chartLat y 1 d) (h1 : IsUnitAt y P' d G) (h2 : ¬IsUnitAt y P d G) :
    ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h := by
  by_contra H
  push Not at H
  obtain ⟨t, ht0, ht⟩ := exists_max y hy P
  have htP' : ∀ u, P'.valuation K' (y ⟨(), u⟩) ≤ P'.valuation K' (y ⟨(), t⟩) := by
    have := H 1 _ (coord_mem y t) (fun u => by simpa using ht u)
    intro u
    simpa using this u
  have hyt : P'.valuation K' (y ⟨(), t⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hyt' : P.valuation K' (y ⟨(), t⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hxR : G / y ⟨(), t⟩ ^ d ∈ chartRingZ y (fun _ => t) := (mem_chartLat_iff y).mp hG t ht0
  have hx' : P'.valuation K' (G / y ⟨(), t⟩ ^ d) = 1 := by
    rw [map_div₀, map_pow]
    exact (div_eq_one_iff_eq (pow_ne_zero _ hyt)).mpr (le_antisymm (le_of_mem y ht0 htP' hG) (h1 t))
  have hx : P.valuation K' (G / y ⟨(), t⟩ ^ d) < 1 := by
    rw [isUnitAt_iff y ht, not_le] at h2
    rw [map_div₀, map_pow]
    exact (div_lt_one₀ (zero_lt_iff.mpr (pow_ne_zero _ hyt'))).mpr h2
  obtain ⟨N, hN, hxN⟩ := exists_pow_sub_one P' hx'
  have hwR : (G / y ⟨(), t⟩ ^ d) ^ N - 1 ∈ chartRingZ y (fun _ => t) :=
    sub_mem (pow_mem hxR N) (one_mem _)
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_chartLat y t ht0 hwR
  have hw : P.valuation K' ((G / y ⟨(), t⟩ ^ d) ^ N - 1) = 1 := by
    rw [← Valuation.map_neg, neg_sub]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_pow]
    exact pow_lt_one₀ zero_le hx (by omega)
  have hu := H k _ hk ((isUnitAt_iff y ht).mpr (le_of_eq (by rw [map_mul, hw, one_mul, map_pow])))
  rw [isUnitAt_iff y htP', map_mul, map_pow] at hu
  have hpos : 0 < P'.valuation K' (y ⟨(), t⟩) ^ k := zero_lt_iff.mpr (pow_ne_zero _ hyt)
  have hlt := mul_lt_mul_of_pos_right hxN hpos
  rw [one_mul] at hlt
  exact absurd hu (not_le.mpr hlt)

theorem exists_avoid (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K'))
    (S : Finset (HeightOneSpectrum (𝓞 K')))
    (hS : ∀ P' ∈ S, ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h) :
    ∃ (k : ℕ) (z : K'), 1 ≤ k ∧ z ∈ chartLat y 1 k ∧ IsUnitAt y P k z ∧
      ∀ P' ∈ S, ¬IsUnitAt y P' k z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨t, -, ht⟩ := exists_max y hy P
    exact ⟨1, _, le_rfl, coord_mem y t, fun u => by simpa using ht u, by simp⟩
  | @insert P'' S hP'' ih =>
    obtain ⟨k, z, hk, hz, hzP, hzS⟩ := ih (fun P' hP' => hS P' (Finset.mem_insert_of_mem hP'))
    obtain ⟨l, h, hh, hhP, hhP''⟩ := hS P'' (Finset.mem_insert_self _ _)
    refine ⟨k + l, z * h, by omega, chartLat_mul_mem y hz hh, hzP.mul y hhP, ?_⟩
    intro P' hP'
    rcases Finset.mem_insert.mp hP' with rfl | hP'
    · have := not_isUnitAt_mul y hy hhP'' hz
      rwa [mul_comm h z, Nat.add_comm l k] at this
    · exact not_isUnitAt_mul y hy (hzS P' hP') hh

theorem exists_unit_all (hy : IsArithVar (mCoordIdeal y) 1) (S : Finset (HeightOneSpectrum (𝓞 K'))) :
    ∃ (d : ℕ) (G : K'), 1 ≤ d ∧ G ≠ 0 ∧ G ∈ chartLat y 1 d ∧ ∀ P ∈ S, IsUnitAt y P d G := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
    exact ⟨1, _, le_rfl, ht, coord_mem y t, by simp⟩
  | @insert P S hP ih =>
    obtain ⟨d, G, hd, hG0, hG, hGS⟩ := ih
    by_cases hu : IsUnitAt y P d G
    · refine ⟨d, G, hd, hG0, hG, fun P' hP' => ?_⟩
      rcases Finset.mem_insert.mp hP' with rfl | hP'
      · exact hu
      · exact hGS P' hP'
    obtain ⟨k, z, hk, hz, hzP, hzS⟩ :=
      exists_avoid y hy P S fun P' hP' => exists_sep y hy hG (hGS P' hP') hu
    have hG' : G ^ k ∈ chartLat y 1 (d * k) := chartLat_pow_mem y hG k
    have hz' : z ^ d ∈ chartLat y 1 (d * k) := by
      rw [Nat.mul_comm]
      exact chartLat_pow_mem y hz d
    have hunitP : IsUnitAt y P (d * k) (G ^ k + z ^ d) := by
      rw [add_comm]
      have h1 : IsUnitAt y P (d * k) (z ^ d) := by
        rw [Nat.mul_comm]
        exact hzP.pow y d
      have h2 : ¬IsUnitAt y P (d * k) (G ^ k) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact not_isUnitAt_pow y hy hu hG k'
      exact isUnitAt_add y hy h1 h2
    refine ⟨d * k, G ^ k + z ^ d, by simpa using Nat.mul_le_mul hd hk, ?_, add_mem hG' hz', ?_⟩
    · intro h0
      obtain ⟨t, ht0, -⟩ := exists_max y hy P
      have := hunitP t
      rw [h0, map_zero] at this
      exact pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0) (le_antisymm this zero_le)
    · intro P' hP'
      rcases Finset.mem_insert.mp hP' with rfl | hP'
      · exact hunitP
      · have h1 : IsUnitAt y P' (d * k) (G ^ k) := (hGS P' hP').pow y k
        have h2 : ¬IsUnitAt y P' (d * k) (z ^ d) := by
          obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          rw [Nat.mul_comm]
          exact not_isUnitAt_pow y hy (hzS P' hP') hz d'
        exact isUnitAt_add y hy h1 h2

omit [Fintype T] [NumberField K'] in

theorem mem_of_isIntegral (W : ValuationSubring K') {x : K'} (hx : IsIntegral ℤ x) : x ∈ W := by
  have : IsIntegral W x := hx.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  rw [← hw]
  exact w.2

omit [Fintype T] in

theorem mem_of_forall_prime (W : ValuationSubring K')
    (hW : ∀ q : ℕ, q.Prime → W.valuation (q : K') = 1) (x : K') : x ∈ W := by
  have hN : ∀ N : ℕ, N ≠ 0 → W.valuation (N : K') = 1 := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => (h rfl).elim
    | one => intro; simp
    | prime p hp => intro; exact hW p hp
    | mul a b ha hb =>
      intro h
      rw [Nat.cast_mul, map_mul, ha (left_ne_zero_of_mul h), hb (right_ne_zero_of_mul h), one_mul]
  obtain ⟨n, hn, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K').mpr (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  have h1 := mem_of_isIntegral W hint
  rw [zsmul_eq_mul] at h1
  have hv : W.valuation (n : K') = 1 := by
    have h2 := hN _ (Int.natAbs_ne_zero.mpr hn)
    rcases Int.natAbs_eq n with h | h
    · rw [h, Int.cast_natCast]
      exact h2
    · rw [h, Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
      exact h2
  rw [← W.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, hv, one_mul] at h1

omit [Fintype T] in

theorem exists_centre (W : ValuationSubring K') {q : ℕ} (hq : q.Prime) (hWq : W.valuation (q : K') < 1) :
    ∃ P : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ P.asIdeal ∧
      ∀ x : K', P.valuation K' x ≤ 1 → x ∈ W := by
  have hO : ∀ a : 𝓞 K', (a : K') ∈ W := fun a => mem_of_isIntegral W (RingOfIntegers.isIntegral_coe a)
  let φ : 𝓞 K' →+* W :=
    { toFun := fun a => ⟨a, hO a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hmem : ∀ a : 𝓞 K', a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal W) ↔ W.valuation (a : K') < 1 :=
    fun a => by rw [Ideal.mem_comap]; exact W.valuation_lt_one_iff (φ a)
  have hqmem : (q : 𝓞 K') ∈ Ideal.comap φ (IsLocalRing.maximalIdeal W) := (hmem _).mpr (by simpa using hWq)
  have hne : Ideal.comap φ (IsLocalRing.maximalIdeal W) ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hqmem
    exact hq.ne_zero (by exact_mod_cast hqmem)
  refine ⟨⟨Ideal.comap φ (IsLocalRing.maximalIdeal W), inferInstance, hne⟩, hqmem, fun x hx => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ x hx
  have hd : W.valuation (algebraMap (𝓞 K') K' d) = 1 :=
    le_antisymm ((W.valuation_le_one_iff _).mpr (hO d)) (not_lt.mp fun h => d.2 ((hmem d).mpr h))
  rw [← W.valuation_le_one_iff]
  have : W.valuation (algebraMap (𝓞 K') K' n) ≤ 1 := (W.valuation_le_one_iff _).mpr (hO n)
  rwa [← hnd, map_mul, hd, mul_one] at this

omit [Fintype T] [NumberField K'] in

theorem finite_centres [NumberField K'] (m : Ideal (curveRing y)) (hm : m.IsMaximal) :
    {P : HeightOneSpectrum (𝓞 K') |
      ∃ q : ℕ, q.Prime ∧ (q : curveRing y) ∈ m ∧ (q : 𝓞 K') ∈ P.asIdeal}.Finite := by
  by_cases h : ∃ q0 : ℕ, q0.Prime ∧ (q0 : curveRing y) ∈ m
  · obtain ⟨q0, hq0, hq0m⟩ := h
    have hne : Ideal.span {(q0 : 𝓞 K')} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq0.ne_zero
    refine (Ideal.finite_factors hne).subset ?_
    rintro P ⟨q, hq, hqm, hqP⟩
    have hqq : q = q0 := by
      by_contra hne'
      obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (q0 : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hq0).mpr hne')
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (a : curveRing y) * q + (b : curveRing y) * q0 = 1 := by
        have := congrArg (Int.cast : ℤ → curveRing y) hab
        push_cast at this
        exact this
      rw [← e]
      exact m.add_mem (m.mul_mem_left _ hqm) (m.mul_mem_left _ hq0m)
    subst hqq
    exact Ideal.dvd_span_singleton.mpr hqP
  · refine Set.finite_empty.subset ?_
    rintro P ⟨q, hq, hqm, -⟩
    exact h ⟨q, hq, hqm⟩

end ClosedPointUnitSectionAlt

theorem ClosedPointUnitSection.proof : ClosedPointUnitSection.Statement := by
  intro T _ K' _ _ y hy m hm
  classical
  have hF := ClosedPointUnitSectionAlt.finite_centres y m hm
  obtain ⟨d, G, hd, hG0, hG, hGS⟩ := ClosedPointUnitSectionAlt.exists_unit_all y hy hF.toFinset
  refine ⟨d, G, hd, hG0, hG, fun W _ hunit u => ?_⟩
  by_cases hq : ∃ q : ℕ, q.Prime ∧ W.valuation (q : K') < 1
  · obtain ⟨q, hq, hWq⟩ := hq
    have hqm : (q : curveRing y) ∈ m := by
      by_contra h
      have := hunit _ h
      push_cast at this
      exact absurd this (ne_of_lt hWq)
    obtain ⟨P, hqP, hPW⟩ := ClosedPointUnitSectionAlt.exists_centre W hq hWq
    apply hPW
    have hPu := hGS P (hF.mem_toFinset.mpr ⟨q, hq, hqm, hqP⟩)
    rw [map_div₀]
    refine (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hG0))).mpr ?_
    rw [map_pow]
    exact hPu u
  · push Not at hq
    refine ClosedPointUnitSectionAlt.mem_of_forall_prime W (fun q hq' => le_antisymm ?_ (hq q hq')) _
    exact (W.valuation_le_one_iff _).mpr (natCast_mem W q)

end

end GroundTheory.Heights₂.Heights
