import Formalism.FrobeniusContraction.StatementB

noncomputable section

open Formalism.WachCohomologyFacts.TopB

namespace Formalism.WachCohomologyFacts.LaurentOrder

variable {k : Type} [Field k]

theorem ord_zero (j : ℤ) : Ord j (0 : LaurentSeries k) := fun i _ => by simp

theorem ord_add {j : ℤ} {x y : LaurentSeries k} (hx : Ord j x) (hy : Ord j y) : Ord j (x + y) :=
  fun i hi => by rw [HahnSeries.coeff_add, hx i hi, hy i hi, add_zero]

theorem ord_sub {j : ℤ} {x y : LaurentSeries k} (hx : Ord j x) (hy : Ord j y) : Ord j (x - y) :=
  fun i hi => by rw [HahnSeries.coeff_sub, hx i hi, hy i hi, sub_zero]

theorem ord_smul {j : ℤ} (r : k) {x : LaurentSeries k} (hx : Ord j x) : Ord j (r • x) :=
  fun i hi => by rw [HahnSeries.coeff_smul, hx i hi, smul_zero]

theorem ord_mono {i j : ℤ} {x : LaurentSeries k} (hx : Ord j x) (h : i ≤ j) : Ord i x :=
  fun t ht => hx t (lt_of_lt_of_le ht h)

theorem ord_sum {ι : Type} (s : Finset ι) {j : ℤ} (f : ι → LaurentSeries k)
    (h : ∀ i ∈ s, Ord j (f i)) : Ord j (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ord_zero j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ord_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ord_succ {j : ℤ} {x : LaurentSeries k} (hx : Ord j x) (h0 : x.coeff j = 0) : Ord (j + 1) x := by
  intro i hi
  rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hi) with h | h
  · exact hx i h
  · rw [h]; exact h0

theorem eq_zero_of_ord_all {x : LaurentSeries k} (h : ∀ j, Ord j x) : x = 0 := by
  ext i; exact h (i + 1) i (by omega)

theorem le_order_of_ord {j : ℤ} {x : LaurentSeries k} (hx0 : x ≠ 0) (hx : Ord j x) : j ≤ x.order := by
  by_contra h
  push Not at h
  exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hx _ h))

theorem ord_mul {i j : ℤ} {x y : LaurentSeries k} (hx : Ord i x) (hy : Ord j y) : Ord (i + j) (x * y) := by
  by_cases hx0 : x = 0
  · subst hx0; simpa using ord_zero (i + j)
  by_cases hy0 : y = 0
  · subst hy0; simpa using ord_zero (i + j)
  intro t ht
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [HahnSeries.order_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hx0)
    (HahnSeries.leadingCoeff_ne_zero.mpr hy0))]
  have := le_order_of_ord hx0 hx
  have := le_order_of_ord hy0 hy
  omega

theorem coeff_mul_ord {i j : ℤ} {x y : LaurentSeries k} (hx : Ord i x) (hy : Ord j y) :
    (x * y).coeff (i + j) = x.coeff i * y.coeff j := by
  by_cases hxi : x.coeff i = 0
  · rw [hxi, zero_mul]
    exact ord_mul (ord_succ hx hxi) hy (i + j) (by omega)
  by_cases hyj : y.coeff j = 0
  · rw [hyj, mul_zero]
    exact ord_mul hx (ord_succ hy hyj) (i + j) (by omega)
  have hx0 : x ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hxi
  have hy0 : y ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hyj
  have ex : x.order = i := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hxi) (le_order_of_ord hx0 hx)
  have ey : y.order = j := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hyj) (le_order_of_ord hy0 hy)
  have := HahnSeries.coeff_mul_order_add_order x y
  rw [ex, ey] at this
  rw [this, HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, ex, ey]

def V (k : Type) [Field k] (m : ℤ) : LaurentSeries k := HahnSeries.single m 1

theorem ord_V (m : ℤ) : Ord m (V k m) := fun i hi => HahnSeries.coeff_single_of_ne (by omega)

theorem coeff_V (m : ℤ) : (V k m).coeff m = 1 := HahnSeries.coeff_single_same _ _

theorem V_mul (m n : ℤ) : V k m * V k n = V k (m + n) := by
  simp [V, HahnSeries.single_mul_single]

theorem V_mul_neg (m : ℤ) : V k m * V k (-m) = 1 := by
  rw [V_mul, add_neg_cancel]; rfl

theorem V_ne_zero (m : ℤ) : V k m ≠ 0 := HahnSeries.single_ne_zero one_ne_zero

theorem coeff_vv_mul (j : ℤ) (x : LaurentSeries k) : (vv k * x).coeff (j + 1) = x.coeff j := by
  rw [vv, HahnSeries.coeff_single_mul_add, one_mul]

theorem algebraMap_eq (r : k) : algebraMap k (LaurentSeries k) r = HahnSeries.single 0 r := by
  first
  | rfl
  | (rw [LaurentSeries.algebraMap_apply]; rfl)

theorem smul_eq_single (r : k) (x : LaurentSeries k) : r • x = HahnSeries.single 0 r * x := by
  ext i
  have := HahnSeries.coeff_single_mul_add (r := r) (x := x) (a := i) (b := (0 : ℤ))
  rw [add_zero] at this
  rw [HahnSeries.coeff_smul, this, smul_eq_mul]

section Psi

variable {ℓ : ℕ} (P : PsiData k ℓ)

theorem φ_single0 (r : k) : P.φ (HahnSeries.single 0 r) = HahnSeries.single 0 r := by
  rw [← algebraMap_eq]; exact P.φ.commutes r

theorem γ_single0 (r : k) : P.γ (HahnSeries.single 0 r) = HahnSeries.single 0 r := by
  rw [← algebraMap_eq]; exact P.γ.commutes r

theorem ψ_smul (r : k) (x : LaurentSeries k) : P.ψ (r • x) = r • P.ψ x := by
  rw [smul_eq_single, ← φ_single0 P, P.ψ_φ, ← smul_eq_single]

theorem psi_order_zero_of_order {c : ℤ} (h1 : 2 - (ℓ : ℤ) ≤ c) (h2 : c ≤ 1) {x : LaurentSeries k} (hx : Ord c x) :
    Ord 0 (P.ψ x) := by
  have : P.ψ x ∈ P.ψ '' {x | Ord c x} := ⟨x, hx, rfl⟩
  rw [P.ψ_low c h1 h2] at this
  exact this

theorem ψ_surj {c : ℤ} (h1 : 2 - (ℓ : ℤ) ≤ c) (h2 : c ≤ 1) {y : LaurentSeries k} (hy : Ord 0 y) :
    ∃ z, Ord c z ∧ P.ψ z = y := by
  have : y ∈ ({x | Ord 0 x} : Set (LaurentSeries k)) := hy
  rw [← P.ψ_low c h1 h2] at this
  obtain ⟨z, hz, e⟩ := this
  exact ⟨z, hz, e⟩

theorem psi_order_one_of_order_two (hℓ : 1 ≤ ℓ) {x : LaurentSeries k} (hx : Ord 2 x) : Ord 1 (P.ψ x) := by
  have : P.ψ x ∈ P.ψ '' {x | Ord 2 x} := ⟨x, hx, rfl⟩
  rw [P.ψ_high 2 le_rfl (by omega)] at this
  exact this

def ψ₁ : k := (P.ψ (vv k)).coeff 0

theorem ord_one : Ord 0 (1 : LaurentSeries k) := fun i hi => by
  rw [HahnSeries.coeff_one, if_neg (by omega)]

theorem ψ_coeff0 (hℓ : 1 ≤ ℓ) {z : LaurentSeries k} (hz : Ord 0 z) :
    (P.ψ z).coeff 0 = z.coeff 0 + z.coeff 1 * ψ₁ P := by
  set r := z - z.coeff 0 • (1 : LaurentSeries k) - z.coeff 1 • vv k with hrdef
  have hr : Ord 2 r := by
    intro i hi
    simp only [r, HahnSeries.coeff_sub, HahnSeries.coeff_smul, HahnSeries.coeff_one, vv,
      HahnSeries.coeff_single, smul_eq_mul]
    rcases (by omega : i < 0 ∨ i = 0 ∨ i = 1) with h | h | h
    · rw [hz i h, if_neg (by omega), if_neg (by omega)]; ring
    · subst h; simp
    · subst h; simp
  have hz' : z = z.coeff 0 • (1 : LaurentSeries k) + z.coeff 1 • vv k + r := by
    rw [hrdef]; abel
  rw [hz', map_add, map_add, ψ_smul, ψ_smul, P.ψ_one, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.coeff_smul, HahnSeries.coeff_smul, psi_order_one_of_order_two P hℓ hr 0 (by norm_num)]
  have e1 : (z.coeff 0 • (1 : LaurentSeries k) + z.coeff 1 • vv k + r).coeff 0 = z.coeff 0 := by
    rw [← hz']
  have e2 : (z.coeff 0 • (1 : LaurentSeries k) + z.coeff 1 • vv k + r).coeff 1 = z.coeff 1 := by
    rw [← hz']
  rw [e1, e2, HahnSeries.coeff_one, if_pos rfl, ψ₁, smul_eq_mul, smul_eq_mul, mul_one, add_zero]

theorem ψ₁_ne (hℓ : 1 ≤ ℓ) : ψ₁ P ≠ 0 := by
  obtain ⟨y, hy, e⟩ := ψ_surj P (c := 1) (by omega) le_rfl (ord_one (k := k))
  have := ψ_coeff0 P hℓ (ord_mono hy (by norm_num))
  rw [e, hy 0 (by norm_num), zero_add, HahnSeries.coeff_one, if_pos rfl] at this
  intro h
  rw [h, mul_zero] at this
  exact one_ne_zero this

def Φ (m : ℤ) : LaurentSeries k := P.φ (V k m)

theorem Φ_mul_neg (m : ℤ) : Φ P m * Φ P (-m) = 1 := by
  rw [Φ, Φ, ← map_mul, V_mul_neg, map_one]

theorem ord_Φ (m : ℤ) : Ord ((ℓ : ℤ) * m) (Φ P m) := P.φ_ord m _ (ord_V m)

theorem ψ_Φ (m : ℤ) (y : LaurentSeries k) : P.ψ (Φ P m * y) = V k m * P.ψ y := P.ψ_φ _ _

theorem Φ_decomp (m : ℤ) (x : LaurentSeries k) : x = Φ P m * (Φ P (-m) * x) := by
  rw [← mul_assoc, Φ_mul_neg, one_mul]

theorem ord_Φneg {b : ℤ} (m : ℤ) {x : LaurentSeries k} (hx : Ord b x) :
    Ord (b - ℓ * m) (Φ P (-m) * x) := by
  have := ord_mul (ord_Φ P (-m)) hx
  have e : (ℓ : ℤ) * -m + b = b - ℓ * m := by ring
  rw [e] at this
  exact this

theorem ψ_decomp (m : ℤ) (x : LaurentSeries k) : P.ψ x = V k m * P.ψ (Φ P (-m) * x) := by
  conv_lhs => rw [Φ_decomp P m x]
  exact ψ_Φ P m _

theorem level_exists (hℓ : 1 ≤ ℓ) (b : ℤ) :
    ∃ m c : ℤ, b = ℓ * m + c ∧ 2 - (ℓ : ℤ) ≤ c ∧ c ≤ 1 := by
  have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have h1 := Int.mul_ediv_add_emod (b + ℓ - 2) ℓ
  have h2 := Int.emod_nonneg (b + ℓ - 2) hpos.ne'
  have h3 := Int.emod_lt_of_pos (b + ℓ - 2) hpos
  refine ⟨(b + ℓ - 2) / ℓ, b - ℓ * ((b + ℓ - 2) / ℓ), by ring, ?_, ?_⟩ <;> linarith

theorem level_one_iff (hℓ : 1 ≤ ℓ) {b m c : ℤ} (hb : b = ℓ * m + c) (h1 : 2 - (ℓ : ℤ) ≤ c) (h2 : c ≤ 1) :
    c = 1 ↔ (ℓ : ℤ) ∣ b - 1 := by
  constructor
  · intro h; subst h; exact ⟨m, by rw [hb]; ring⟩
  · intro h
    have hd : (ℓ : ℤ) ∣ c - 1 := by
      have : c - 1 = (b - 1) - ℓ * m := by rw [hb]; ring
      rw [this]; exact dvd_sub h (dvd_mul_right _ _)
    obtain ⟨t, ht⟩ := hd
    have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
    rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
    · have : (ℓ : ℤ) * t ≤ -ℓ := by nlinarith
      linarith
    · subst ht0; linarith
    · have : (ℓ : ℤ) * t ≥ ℓ := by nlinarith
      linarith

theorem ψ_cont (hℓ : 2 ≤ ℓ) (N : ℤ) {x : LaurentSeries k} (hx : Ord (ℓ * N) x) : Ord N (P.ψ x) := by
  rw [ψ_decomp P N x]
  have hw := ord_Φneg P N hx
  rw [sub_self] at hw
  have := ord_mul (ord_V (k := k) N) (psi_order_zero_of_order P (c := 0) (by omega) (by norm_num) hw)
  rwa [add_zero] at this

theorem ψ_level1 (hℓ : 1 ≤ ℓ) {b : ℤ} (hd : (ℓ : ℤ) ∣ b - 1) {x : LaurentSeries k} (hx : Ord b x)
    (hψ : P.ψ x = 0) : x.coeff b = 0 := by
  obtain ⟨m, c, hb, h1, h2⟩ := level_exists hℓ b
  have hc : c = 1 := (level_one_iff hℓ hb h1 h2).mpr hd
  have hw : Ord 1 (Φ P (-m) * x) := by
    have := ord_Φneg P m hx
    have e : b - ℓ * m = 1 := by rw [hb, hc]; ring
    rwa [e] at this
  have hψw : P.ψ (Φ P (-m) * x) = 0 := by
    have := ψ_decomp P m x
    rw [hψ] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (V_ne_zero m)
    · exact h
  have hc0 := ψ_coeff0 P hℓ (ord_mono hw (by norm_num))
  rw [hψw, hw 0 (by norm_num), zero_add, HahnSeries.coeff_zero] at hc0
  have hw1 : (Φ P (-m) * x).coeff 1 = 0 := by
    rcases mul_eq_zero.mp hc0.symm with h | h
    · exact h
    · exact absurd h (ψ₁_ne P hℓ)
  rw [Φ_decomp P m x, hb, hc, coeff_mul_ord (ord_Φ P m) hw, hw1, mul_zero]

theorem ψ_lift (hℓ : 1 ≤ ℓ) {b : ℤ} (hd : ¬ (ℓ : ℤ) ∣ b - 1) (α : k) :
    ∃ x : LaurentSeries k, Ord b x ∧ P.ψ x = 0 ∧ x.coeff b = α := by
  obtain ⟨m, c, hb, h1, h2⟩ := level_exists hℓ b
  have hc : c ≤ 0 := by
    rcases lt_or_eq_of_le h2 with h | h
    · omega
    · exact absurd ((level_one_iff hℓ hb h1 h2).mp h) hd
  set y : LaurentSeries k := α • V k b
  have hy : Ord b y := ord_smul α (ord_V b)
  have hw : Ord c (Φ P (-m) * y) := by
    have := ord_Φneg P m hy
    have e : b - ℓ * m = c := by rw [hb]; ring
    rwa [e] at this
  obtain ⟨z, hz, hze⟩ := ψ_surj P (c := c + 1) (by omega) (by omega) (psi_order_zero_of_order P h1 h2 hw)
  refine ⟨y - Φ P m * z, ?_, ?_, ?_⟩
  · have := ord_mul (ord_Φ P m) hz
    have e : (ℓ : ℤ) * m + (c + 1) = b + 1 := by rw [hb]; ring
    rw [e] at this
    exact ord_sub hy (ord_mono this (by omega))
  · rw [map_sub, ψ_Φ, hze, ← ψ_decomp, sub_self]
  · have := ord_mul (ord_Φ P m) hz
    have e : (ℓ : ℤ) * m + (c + 1) = b + 1 := by rw [hb]; ring
    rw [e] at this
    rw [HahnSeries.coeff_sub, this b (by omega), sub_zero, HahnSeries.coeff_smul, coeff_V, smul_eq_mul,
      mul_one]

end Psi

section Gam

variable {ℓ : ℕ} (P : PsiData k ℓ)

theorem T_ord {j : ℤ} {x : LaurentSeries k} (hx : Ord j x) : Ord (j + 1) (P.γ x - x) :=
  (P.γ_lead j x hx).1

theorem T_coeff {j : ℤ} {x : LaurentSeries k} (hx : Ord j x) :
    (P.γ x - x).coeff (j + 1) = (j : k) * P.c₀ * x.coeff j := by
  have h := (P.γ_lead j x hx).2 (j + 1) (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_smul, coeff_vv_mul, smul_eq_mul, sub_eq_zero] at h
  exact h

theorem γ_ord {j : ℤ} {x : LaurentSeries k} (hx : Ord j x) : Ord j (P.γ x) := by
  have := ord_add (ord_mono (T_ord P hx) (by omega)) hx
  rwa [sub_add_cancel] at this

theorem ψT {x : LaurentSeries k} (h : P.ψ x = 0) : P.ψ (P.γ x - x) = 0 := by
  rw [map_sub, P.ψ_γ, h, map_zero, sub_zero]

def κ (b : ℤ) : k := if (ℓ : ℤ) ∣ b then -(P.c₀ / ψ₁ P) else (b : k) * P.c₀

def cb (ℓ : ℕ) (b : ℤ) : ℤ := if (ℓ : ℤ) ∣ b then b + 2 else b + 1

theorem cb_le (ℓ : ℕ) (b : ℤ) : cb ℓ b ≤ b + 2 := by unfold cb; split_ifs <;> omega

theorem T_zero (hℓ : 3 ≤ ℓ) {b : ℤ} (hd : (ℓ : ℤ) ∣ b) {x : LaurentSeries k} (hx : Ord b x)
    (hψ : P.ψ x = 0) :
    Ord (b + 2) (P.γ x - x) ∧ (P.γ x - x).coeff (b + 2) = -(P.c₀ / ψ₁ P) * x.coeff b := by
  obtain ⟨m, rfl⟩ := hd
  have hz : Ord 0 (Φ P (-m) * x) := by
    have := ord_Φneg P m hx; rwa [sub_self] at this
  have hψz : P.ψ (Φ P (-m) * x) = 0 := by
    have := ψ_decomp P m x
    rw [hψ] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (V_ne_zero m)
    · exact h
  have hxz : x = Φ P m * (Φ P (-m) * x) := Φ_decomp P m x
  generalize Φ P (-m) * x = z at hz hψz hxz
  have hz01 : z.coeff 0 + z.coeff 1 * ψ₁ P = 0 := by
    rw [← ψ_coeff0 P (by omega) hz, hψz, HahnSeries.coeff_zero]
  have hdd : Ord (m + 1) (P.γ (V k m) - V k m) := T_ord P (ord_V m)
  have hγΦ : P.γ (Φ P m) = Φ P m + P.φ (P.γ (V k m) - V k m) := by
    rw [Φ, P.γ_φ, map_sub]; ring
  have key : P.γ x - x = Φ P m * (P.γ z - z) + P.φ (P.γ (V k m) - V k m) * P.γ z := by
    rw [hxz, map_mul, hγΦ]; ring
  set y := z - HahnSeries.single 0 (z.coeff 0) with hydef
  have hyz : P.γ z - z = P.γ y - y := by
    rw [hydef, map_sub, γ_single0]; ring
  have hy : Ord 1 y := by
    intro i hi
    rw [hydef, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rcases (by omega : i < 0 ∨ i = 0) with h | h
    · rw [hz i h, if_neg (by omega), sub_zero]
    · subst h; simp
  have hy1 : y.coeff 1 = z.coeff 1 := by
    rw [hydef, HahnSeries.coeff_sub, HahnSeries.coeff_single_of_ne (by norm_num), sub_zero]
  have hT2 : Ord 2 (P.γ y - y) := by
    have := T_ord P hy; rwa [show (1 : ℤ) + 1 = 2 by norm_num] at this
  have hTc : (P.γ y - y).coeff 2 = P.c₀ * z.coeff 1 := by
    have := T_coeff P hy
    rw [show (1 : ℤ) + 1 = 2 by norm_num, Int.cast_one, one_mul, hy1] at this
    exact this
  have h1 := ord_mul (ord_Φ P m) hT2
  have h2 := ord_mul (P.φ_ord (m + 1) _ hdd) (γ_ord P hz)
  have e2 : (ℓ : ℤ) * (m + 1) + 0 = ℓ * m + ℓ := by ring
  rw [e2] at h2
  rw [key, ← hyz] at *
  refine ⟨ord_add h1 (ord_mono h2 (by omega)), ?_⟩
  rw [HahnSeries.coeff_add, coeff_mul_ord (ord_Φ P m) hT2, h2 _ (by omega), add_zero, hyz, hTc]
  conv_rhs => rw [hxz]
  have e0 := coeff_mul_ord (ord_Φ P m) hz
  rw [add_zero] at e0
  rw [e0]
  have hz0 : z.coeff 0 = -(z.coeff 1 * ψ₁ P) := eq_neg_of_add_eq_zero_left hz01
  rw [hz0]
  have := ψ₁_ne P (by omega)
  field_simp

theorem T_lead (hℓ : 3 ≤ ℓ) {b : ℤ} {x : LaurentSeries k} (hx : Ord b x) (hψ : P.ψ x = 0) :
    Ord (cb ℓ b) (P.γ x - x) ∧ (P.γ x - x).coeff (cb ℓ b) = κ P b * x.coeff b := by
  unfold cb κ
  split_ifs with h
  · exact T_zero P hℓ h hx hψ
  · exact ⟨T_ord P hx, T_coeff P hx⟩

theorem κ_ne [CharP k ℓ] (hℓ : 2 ≤ ℓ) (b : ℤ) : κ P b ≠ 0 := by
  unfold κ
  split_ifs with h
  · exact neg_ne_zero.mpr (div_ne_zero P.hc₀ (ψ₁_ne P (by omega)))
  · refine mul_ne_zero ?_ P.hc₀
    rw [Ne, CharP.intCast_eq_zero_iff k ℓ b]
    exact h

variable {n : ℕ} (g : Fin n → Fin n → LaurentSeries k)

def Gam (x : Fin n → LaurentSeries k) : Fin n → LaurentSeries k :=
  fun m => ∑ j, P.γ (x j) * P.φ (g j m)

def Eg (x : Fin n → LaurentSeries k) (m : Fin n) : LaurentSeries k :=
  ∑ j, P.γ (x j) * P.φ (g j m - if j = m then 1 else 0)

theorem φ_sub_δ (j m : Fin n) :
    P.φ (g j m - if j = m then 1 else 0) = P.φ (g j m) - if j = m then 1 else 0 := by
  split_ifs <;> simp

theorem Gam_sub_eq (x : Fin n → LaurentSeries k) (m : Fin n) :
    (Gam P g x - x) m = (P.γ (x m) - x m) + Eg P g x m := by
  simp only [Gam, Eg, Pi.sub_apply, φ_sub_δ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem Eg_ord (hg : ∀ i j, Ord 1 (g i j - if i = j then 1 else 0)) {b : ℤ}
    {x : Fin n → LaurentSeries k} (hx : ∀ j, Ord b (x j)) (m : Fin n) :
    Ord (b + ℓ) (Eg P g x m) := by
  apply ord_sum
  intro j _
  have := ord_mul (γ_ord P (hx j)) (P.φ_ord 1 _ (hg j m))
  rwa [mul_one] at this

theorem Gam_ψ {x : Fin n → LaurentSeries k} (hx : ∀ j, P.ψ (x j) = 0) (m : Fin n) :
    P.ψ ((Gam P g x - x) m) = 0 := by
  rw [Pi.sub_apply, map_sub, hx m, sub_zero, Gam, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [mul_comm, P.ψ_φ, P.ψ_γ, hx j, map_zero, mul_zero]

theorem Gam_add (x y : Fin n → LaurentSeries k) : Gam P g (x + y) = Gam P g x + Gam P g y := by
  funext m
  simp [Gam, map_add, add_mul, Finset.sum_add_distrib]

theorem Gam_sub (x y : Fin n → LaurentSeries k) : Gam P g (x - y) = Gam P g x - Gam P g y := by
  funext m
  simp [Gam, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem Gam_zero : Gam P g (0 : Fin n → LaurentSeries k) = 0 := by
  funext m
  simp [Gam]

end Gam

section Main

variable {ℓ : ℕ} (P : PsiData k ℓ) {n : ℕ} (g : Fin n → Fin n → LaurentSeries k)

def XS (b : ℤ) (x : Fin n → LaurentSeries k) : Prop := ∀ j, Ord b (x j) ∧ P.ψ (x j) = 0

theorem XS_zero (b : ℤ) : XS P b (0 : Fin n → LaurentSeries k) :=
  fun j => ⟨ord_zero b, by simp⟩

theorem XS_add {b : ℤ} {x y : Fin n → LaurentSeries k} (hx : XS P b x) (hy : XS P b y) :
    XS P b (x + y) := fun j =>
  ⟨ord_add (hx j).1 (hy j).1, by rw [Pi.add_apply, map_add, (hx j).2, (hy j).2, add_zero]⟩

theorem XS_mono {b c : ℤ} {x : Fin n → LaurentSeries k} (hx : XS P b x) (h : c ≤ b) : XS P c x :=
  fun j => ⟨ord_mono (hx j).1 h, (hx j).2⟩

variable (hg : ∀ i j, Ord 1 (g i j - if i = j then 1 else 0))
include hg

theorem Gam_pres (hℓ : 1 ≤ ℓ) {b : ℤ} {x : Fin n → LaurentSeries k} (hx : ∀ j, Ord b (x j))
    (m : Fin n) : Ord b ((Gam P g x - x) m) := by
  rw [Gam_sub_eq]
  exact ord_add (ord_mono (T_ord P (hx m)) (by omega)) (ord_mono (Eg_ord P g hg hx m) (by omega))

theorem Gam_lead (hℓ : 3 ≤ ℓ) {b : ℤ} {x : Fin n → LaurentSeries k} (hx : XS P b x) (m : Fin n) :
    Ord (cb ℓ b) ((Gam P g x - x) m) ∧
      ((Gam P g x - x) m).coeff (cb ℓ b) = κ P b * (x m).coeff b := by
  rw [Gam_sub_eq]
  obtain ⟨h1, h2⟩ := T_lead P hℓ (hx m).1 (hx m).2
  have hE := Eg_ord P g hg (fun j => (hx j).1) m
  have hle := cb_le ℓ b
  refine ⟨ord_add h1 (ord_mono hE (by omega)), ?_⟩
  rw [HahnSeries.coeff_add, h2, hE _ (by omega), add_zero]

omit hg in
theorem level1_X (hℓ : 1 ≤ ℓ) {b : ℤ} (hd : (ℓ : ℤ) ∣ b - 1) {x : Fin n → LaurentSeries k}
    (hx : XS P b x) : XS P (b + 1) x :=
  fun j => ⟨ord_succ (hx j).1 (ψ_level1 P hℓ hd (hx j).1 (hx j).2), (hx j).2⟩

theorem inj [CharP k ℓ] (hℓ : 3 ≤ ℓ) {a : ℤ} {x : Fin n → LaurentSeries k} (hx : XS P a x)
    (hfix : Gam P g x = x) : x = 0 := by
  have hall : ∀ N : ℕ, XS P (a + N) x := by
    intro N
    induction N with
    | zero => simpa using hx
    | succ N ih =>
      rw [Nat.cast_succ, ← add_assoc]
      by_cases hd : (ℓ : ℤ) ∣ a + N - 1
      · exact level1_X P (by omega) hd ih
      · intro j
        refine ⟨ord_succ (ih j).1 ?_, (ih j).2⟩
        obtain ⟨_, h2⟩ := Gam_lead P g hg hℓ ih j
        rw [hfix, sub_self, Pi.zero_apply, HahnSeries.coeff_zero] at h2
        rcases mul_eq_zero.mp h2.symm with h | h
        · exact absurd h (κ_ne P (by omega) _)
        · exact h
  funext j
  apply eq_zero_of_ord_all
  intro t
  exact ord_mono (hall (Int.toNat (t - a)) j).1 (by omega)

theorem surj_step [CharP k ℓ] (hℓ : 5 ≤ ℓ) {a : ℤ} (ha : ¬ (ℓ : ℤ) ∣ a - 1) {c : ℤ} (hc : a + 1 ≤ c)
    {r : Fin n → LaurentSeries k} (hr : XS P c r) :
    ∃ D : Fin n → LaurentSeries k, XS P a D ∧ (∀ j, Ord (c - 2) (D j)) ∧
      XS P (c + 1) (r - (Gam P g D - D)) := by
  by_cases hc1 : (ℓ : ℤ) ∣ c - 1
  · refine ⟨0, XS_zero P a, fun j => ord_zero _, ?_⟩
    rw [Gam_zero, sub_zero, sub_zero]
    exact level1_X P (by omega) hc1 hr

  obtain ⟨b, hbc, hb1, hba, hb2⟩ : ∃ b : ℤ, cb ℓ b = c ∧ ¬ (ℓ : ℤ) ∣ b - 1 ∧ a ≤ b ∧ c - 2 ≤ b := by
    by_cases hc2 : (ℓ : ℤ) ∣ c - 2
    · refine ⟨c - 2, ?_, ?_, ?_, le_rfl⟩
      · unfold cb; rw [if_pos hc2]; ring
      · intro h
        have : (ℓ : ℤ) ∣ 1 := by
          have := dvd_sub hc2 h
          rwa [show c - 2 - (c - 2 - 1) = 1 by ring] at this
        have := Int.le_of_dvd one_pos this
        omega
      · by_contra hlt
        have : c = a + 1 := by omega
        subst this
        exact ha (by rwa [show a + 1 - 2 = a - 1 by ring] at hc2)
    · refine ⟨c - 1, ?_, ?_, by omega, by omega⟩
      · unfold cb; rw [if_neg (by rwa [show c - 1 = c - 1 by rfl])]; ring
      · rwa [show c - 1 - 1 = c - 2 by ring]
  have hκ := κ_ne P (by omega) b
  have hlift : ∀ j, ∃ x : LaurentSeries k, Ord b x ∧ P.ψ x = 0 ∧ x.coeff b = (r j).coeff c / κ P b :=
    fun j => ψ_lift P (by omega) hb1 _
  choose D hD1 hD2 hD3 using hlift
  have hDX : XS P b D := fun j => ⟨hD1 j, hD2 j⟩
  refine ⟨D, XS_mono P hDX hba, fun j => ord_mono (hD1 j) hb2, ?_⟩
  intro j
  obtain ⟨l1, l2⟩ := Gam_lead P g hg (by omega) hDX j
  rw [hbc] at l1 l2
  refine ⟨ord_succ (ord_sub (hr j).1 l1) ?_, ?_⟩
  · rw [Pi.sub_apply, HahnSeries.coeff_sub, l2, hD3 j, mul_div_cancel₀ _ hκ, sub_self]
  · rw [Pi.sub_apply, map_sub, (hr j).2, Gam_ψ P g (fun j => (hD2 j)) j, sub_zero]

theorem surj [CharP k ℓ] (hℓ : 5 ≤ ℓ) {a : ℤ} (ha : ¬ (ℓ : ℤ) ∣ a - 1) {y : Fin n → LaurentSeries k}
    (hy : XS P (a + 1) y) : ∃ x, XS P a x ∧ Gam P g x - x = y := by
  have step : ∀ (N : ℕ) (S : Fin n → LaurentSeries k),
      (XS P a S ∧ XS P (a + 1 + N) (y - (Gam P g S - S))) →
      ∃ D : Fin n → LaurentSeries k, (∀ j, Ord (a + N - 1) (D j)) ∧
        (XS P a (S + D) ∧ XS P (a + 1 + (N + 1 : ℕ)) (y - (Gam P g (S + D) - (S + D)))) := by
    intro N S ⟨hS1, hS2⟩
    obtain ⟨D, hD1, hD2, hD3⟩ := surj_step P g hg hℓ ha (c := a + 1 + N) (by omega) hS2
    refine ⟨D, fun j => ?_, XS_add P hS1 hD1, ?_⟩
    · have := hD2 j; rwa [show a + 1 + (N : ℤ) - 2 = a + N - 1 by ring] at this
    · have e : y - (Gam P g (S + D) - (S + D)) = y - (Gam P g S - S) - (Gam P g D - D) := by
        rw [Gam_add]; abel
      rw [e, Nat.cast_succ, ← add_assoc]
      exact hD3
  choose! Dn hDn1 hDn2 using step
  let seq : ℕ → Fin n → LaurentSeries k := fun N => Nat.rec 0 (fun N S => S + Dn N S) N
  have seq_succ : ∀ N, seq (N + 1) = seq N + Dn N (seq N) := fun N => rfl
  have inv : ∀ N, XS P a (seq N) ∧ XS P (a + 1 + N) (y - (Gam P g (seq N) - seq N)) := by
    intro N
    induction N with
    | zero =>
      refine ⟨XS_zero P a, ?_⟩
      show XS P (a + 1 + ((0 : ℕ) : ℤ)) (y - (Gam P g 0 - 0))
      rw [Gam_zero, sub_zero, sub_zero, Nat.cast_zero, add_zero]
      exact hy
    | succ N ih => rw [seq_succ]; exact hDn2 N _ ih
  have diff : ∀ N M : ℕ, N ≤ M → ∀ j, Ord (a + N - 1) ((seq M - seq N) j) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => intro j; rw [sub_self]; exact ord_zero _
    | succ M hNM ih =>
      intro j
      rw [seq_succ, show seq M + Dn M (seq M) - seq N = (seq M - seq N) + Dn M (seq M) by abel,
        Pi.add_apply]
      exact ord_add (ih j) (ord_mono (hDn1 M _ (inv M) j) (by omega))
  have agree : ∀ N M : ℕ, ∀ j, ∀ i : ℤ, i < a + N - 1 → i < a + M - 1 →
      (seq M j).coeff i = (seq N j).coeff i := by
    intro N M j i hN hM
    rcases le_total N M with h | h
    · have := diff N M h j i hN
      rwa [Pi.sub_apply, HahnSeries.coeff_sub, sub_eq_zero] at this
    · have := diff M N h j i hM
      rw [Pi.sub_apply, HahnSeries.coeff_sub, sub_eq_zero] at this
      exact this.symm
  let f : Fin n → ℤ → k := fun j i => (seq (Int.toNat (i - a + 2)) j).coeff i
  have hf0 : ∀ j i, i < a → f j i = 0 := fun j i hi => ((inv _).1 j).1 i hi
  have hbdd : ∀ j, BddBelow (Function.support (f j)) := by
    intro j
    refine ⟨a, fun i hi => ?_⟩
    by_contra h
    exact hi (hf0 j i (by omega))
  let xl : Fin n → LaurentSeries k := fun j => HahnSeries.ofSuppBddBelow (f j) (hbdd j)
  have close : ∀ (N : ℕ) j, Ord (a + N - 1) ((xl - seq N) j) := by
    intro N j i hi
    rw [Pi.sub_apply, HahnSeries.coeff_sub, sub_eq_zero]
    show f j i = _
    exact agree N _ j i hi (by omega)
  have hxl : XS P a xl := by
    intro j
    refine ⟨fun i hi => hf0 j i hi, ?_⟩
    apply eq_zero_of_ord_all
    intro t
    have hc := close (Int.toNat (ℓ * t - a + 1)) j
    have hψ := ψ_cont P (by omega) t (ord_mono hc (by omega))
    rw [Pi.sub_apply, map_sub, ((inv _).1 j).2, sub_zero] at hψ
    exact hψ
  refine ⟨xl, hxl, ?_⟩
  funext m
  rw [← sub_eq_zero]
  apply eq_zero_of_ord_all
  intro t
  set N := Int.toNat (t - a + 1)
  have e : (Gam P g xl - xl) m - y m =
      (Gam P g (xl - seq N) - (xl - seq N)) m - (y - (Gam P g (seq N) - seq N)) m := by
    rw [Gam_sub]; simp only [Pi.sub_apply]; abel
  rw [e]
  refine ord_mono (ord_sub (Gam_pres P g hg (by omega) (close N) m)
    (ord_mono ((inv N).2 m).1 (by omega))) (by omega)

end Main

end Formalism.WachCohomologyFacts.LaurentOrder
