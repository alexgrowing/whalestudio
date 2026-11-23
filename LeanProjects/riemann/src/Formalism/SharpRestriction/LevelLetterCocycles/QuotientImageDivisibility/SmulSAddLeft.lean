import Mathlib

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def LB (m : ℤ) (f : ℤ → V) : Prop := ∀ k < m, f k = 0

def smulS (g : PowerSeries LL) (f : ℤ → V) : ℤ → V :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem smulS_eq_sum {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : smulS g f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (k - j) := by
  show ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j) = _
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  apply hj
  rw [hf (k - j) (by omega), smul_zero]

theorem LB_mono {m m' : ℤ} {f : ℤ → V} (hf : LB m f) (h : m' ≤ m) : LB m' f := by
  intro k hk
  exact hf k (lt_of_lt_of_le hk h)

theorem LB_smulS {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) : LB m (smulS g f) := by
  intro k hk
  rw [smulS_eq_sum hf g k 0 (by omega)]
  simp

theorem LB_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f + f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f - f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) : LB m (c • f) := by
  intro k hk
  simp [hf k hk]

theorem LB_min {m m' : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m' f') :
    LB (min m m') f ∧ LB (min m m') f' := by
  exact ⟨LB_mono hf (min_le_left _ _), LB_mono hf' (min_le_right _ _)⟩

private theorem exists_nat_gt_int_sub (k m : ℤ) : ∃ N : ℕ, k - m < N := by
  first
  | exact exists_nat_gt (k - m)
  | exact ⟨(k - m).toNat + 1, by omega⟩
  | exact ⟨(k - m).toNat + 1, by have := Int.self_le_toNat (k - m); omega⟩

theorem smulS_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f + f') = smulS g f + smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.add_apply, smulS_eq_sum (LB_add hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, smul_add]

theorem smulS_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f - f') = smulS g f - smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.sub_apply, smulS_eq_sum (LB_sub hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, smul_sub]

theorem smulS_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (c : LL) :
    smulS g (c • f) = c • smulS g f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.smul_apply, smulS_eq_sum (LB_smul hf c) g k N hN,
    smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

theorem smulS_add_left {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g + h) f = smulS g f + smulS h f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.add_apply, smulS_eq_sum hf (g + h) k N hN, smulS_eq_sum hf g k N hN,
    smulS_eq_sum hf h k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, add_smul]

private theorem smulS_C_eq_smul_of_LB {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [PowerSeries.coeff_C, hj]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

theorem smulS_one {m : ℤ} {f : ℤ → V} (hf : LB m f) : smulS (1 : PowerSeries LL) f = f := by
  first
  | simpa using smulS_C_eq_smul_of_LB hf (1 : LL)
  | (have h1 := smulS_C_eq_smul_of_LB hf (1 : LL); rwa [map_one, one_smul] at h1)

theorem smulS_C {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  exact smulS_C_eq_smul_of_LB hf c

theorem smulS_X_pow {m : ℤ} {f : ℤ → V} (hf : LB m f) (K : ℕ) :
    smulS ((PowerSeries.X : PowerSeries LL) ^ K) f = fun k => f (k - K) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + K + 1) (by omega), Finset.sum_eq_single K]
  · simp [PowerSeries.coeff_X_pow]
  · intro j _ hj
    simp [PowerSeries.coeff_X_pow, hj]
  · intro hK
    exact absurd (Finset.mem_range.mpr (by omega)) hK

theorem smulS_mul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g * h) f = smulS g (smulS h f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  have hR : ∀ i : ℕ, smulS h f (k - i) =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j h • f (k - i - j) :=
    fun i => smulS_eq_sum hf h (k - i) N (by omega)
  have hzero : ∀ i j : ℕ, N ≤ i + j → f (k - i - j) = 0 := fun i j hij => hf _ (by omega)
  calc smulS (g * h) f k
      = ∑ n ∈ Finset.range N, PowerSeries.coeff n (g * h) • f (k - n) :=
        smulS_eq_sum hf _ k N hN
    _ = ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [PowerSeries.coeff_mul, Finset.sum_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := by
          simp only [Finset.mem_range, Nat.succ_eq_add_one] at hi
          omega
        have e : k - (n : ℤ) = k - i - ((n - i : ℕ) : ℤ) := by omega
        rw [e]
        try rfl
    _ = ∑ i ∈ Finset.range N, ∑ n ∈ Finset.Ico i N,
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) :=
        Finset.sum_comm' fun n i => by
          simp only [Finset.mem_range, Finset.mem_Ico]
          constructor <;> intro hh <;> omega
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i),
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Nat.add_sub_cancel_left]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        apply Finset.sum_subset
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        · intro j hj hj'
          simp only [Finset.mem_range, not_lt] at hj hj'
          simp only [hzero i j (by omega), smul_zero]
    _ = smulS g (smulS h f) k := by
        rw [smulS_eq_sum (LB_smulS hf h) g k N hN]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hR, Finset.smul_sum, smul_smul]

theorem smulS_inv {m : ℤ} {f : ℤ → V} (hf : LB m f) (u : PowerSeries LL)
    (hu : PowerSeries.constantCoeff u ≠ 0) : smulS u⁻¹ (smulS u f) = f := by
  have h1 : u⁻¹ * u = 1 := by
    first
    | exact PowerSeries.inv_mul_cancel u hu
    | exact PowerSeries.inv_mul_cancel hu
    | exact PowerSeries.inv_mul_cancel _ hu
    | (rw [mul_comm]; exact PowerSeries.mul_inv_cancel u hu)
  rw [← smulS_mul hf, h1, smulS_one hf]

def Dg (Fil : ℤ → Submodule LL V) (s : ℤ) (f : ℤ → V) : Prop := ∀ k, f k ∈ Fil (s - k)

theorem Dg_smulS {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {m s : ℤ} {f : ℤ → V}
    (hf : LB m f) (hD : Dg Fil s f) (g : PowerSeries LL) : Dg Fil s (smulS g f) := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf g k N hN]
  refine sum_mem fun j _ => Submodule.smul_mem _ _ ?_
  exact hF (by omega : s - k ≤ s - (k - (j : ℤ))) (hD (k - j))

theorem Dg_add {Fil : ℤ → Submodule LL V} {s : ℤ} {f f' : ℤ → V} (h : Dg Fil s f)
    (h' : Dg Fil s f') : Dg Fil s (f + f') := by
  intro k
  rw [Pi.add_apply]
  exact add_mem (h k) (h' k)

theorem Dg_sub {Fil : ℤ → Submodule LL V} {s : ℤ} {f f' : ℤ → V} (h : Dg Fil s f)
    (h' : Dg Fil s f') : Dg Fil s (f - f') := by
  intro k
  rw [Pi.sub_apply]
  exact sub_mem (h k) (h' k)

theorem Dg_smul {Fil : ℤ → Submodule LL V} {s : ℤ} {f : ℤ → V} (h : Dg Fil s f) (c : LL) :
    Dg Fil s (c • f) := by
  intro k
  rw [Pi.smul_apply]
  exact Submodule.smul_mem _ c (h k)

def resc (χ : LL) (f : ℤ → V) : ℤ → V := fun k => (χ ^ k) • f k

theorem LB_resc {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) : LB m (resc χ f) := by
  intro k hk
  show (χ ^ k) • f k = 0
  rw [hf k hk, smul_zero]

theorem smulS_rescale {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) (hχ : χ ≠ 0)
    (g : PowerSeries LL) : smulS (PowerSeries.rescale χ g) (resc χ f) = resc χ (smulS g f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum (LB_resc hf χ) _ k N hN]
  show _ = χ ^ k • smulS g f k
  rw [smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : χ ^ j * χ ^ (k - (j : ℤ)) = χ ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hχ]
    congr 1
    omega
  show PowerSeries.coeff j (PowerSeries.rescale χ g) • (χ ^ (k - (j : ℤ)) • f (k - j)) =
    χ ^ k • (PowerSeries.coeff j g • f (k - j))
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul, mul_right_comm, e]

theorem Dg_resc {Fil : ℤ → Submodule LL V} {s : ℤ} {f : ℤ → V} (h : Dg Fil s f) (χ : LL) :
    Dg Fil s (resc χ f) := by
  intro k
  show (χ ^ k) • f k ∈ Fil (s - k)
  exact Submodule.smul_mem _ _ (h k)

end Formalism.MainNotions.N.Pv.LocalLengthBound.Ser
