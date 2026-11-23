import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Resolvent

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def resid (a : Fin n → ℂ) (s : Fin n) : ℂ := ∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')

def ratioV (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def ratioVd (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s')

theorem prod_one_add_eq_of_resolvent {ι : Type} [DecidableEq ι] (S : Finset ι) :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (a : ι → ℂ) (_ : Set.InjOn a S) (g : ι → R)
      (_ : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (a t - a s) • (g t * g s) = g t - g s),
      ∏ s ∈ S, (1 + g s) =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s := by
  refine Finset.induction_on S ?_ ?_
  · intro R _ _ a _ g _
    simp
  · intro t S ht ih R _ _ a ha g hg
    have hinj : ∀ x ∈ insert t S, ∀ y ∈ insert t S, a x = a y → x = y :=
      fun x hx y hy h => ha (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
    have haS : Set.InjOn a ↑S := fun x hx y hy h =>
      hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) h
    have hne : ∀ s ∈ S, a t - a s ≠ 0 := fun s hs h =>
      ht ((hinj t (Finset.mem_insert_self t S) s (Finset.mem_insert_of_mem hs) (sub_eq_zero.mp h)) ▸ hs)
    have hgS : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → (a s' - a s) • (g s' * g s) = g s' - g s :=
      fun s hs s' hs' h => hg s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') h
    have hC : ∏ s ∈ S, (1 + 1 / (a t - a s)) = 1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • (1 / (a t - a s)) :=
      ih ℂ a haS (fun s => 1 / (a t - a s)) (fun s hs s' hs' _ => by
        have h1 := hne s hs
        have h2 := hne s' hs'
        simp only [smul_eq_mul]
        field_simp
        ring)
    have hR := ih R a haS g hgS
    have hts : ∀ s ∈ S, g t * g s = (1 / (a t - a s)) • (g t - g s) := by
      intro s hs
      have h' := hg s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_self t S) (fun h => ht (h ▸ hs))
      rw [← h', smul_smul, one_div, inv_mul_cancel₀ (hne s hs), one_smul]
    have hcs : ∀ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) =
        (a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) := by
      intro s hs
      have hst : t ≠ s := fun h => ht (h ▸ hs)
      rw [Finset.erase_insert_of_ne hst, Finset.prod_insert (fun h => ht (Finset.mem_of_mem_erase h))]
    have hct : ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s)) := by
      calc ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') = ∏ s ∈ S, (1 + 1 / (a t - a s)) :=
            Finset.prod_congr rfl fun s hs => by
              have := hne s hs
              field_simp
        _ = _ := by rw [hC]; simp only [smul_eq_mul]
    have hper : ∀ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s =
        (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [← sub_smul]
      congr 1
      have h1 := hne s hs
      have h2 : a s - a t ≠ 0 := fun h => h1 (by linear_combination -h)
      field_simp
      ring
    have hmul : ∀ s ∈ S, g t * ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s) =
        ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g t - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [mul_smul_comm, hts s hs, smul_smul, smul_sub]
    have hsum2 : ∑ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) • g s =
        ∑ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s :=
      Finset.sum_congr rfl fun s hs => by rw [hcs s hs]
    rw [Finset.prod_insert ht, hR, Finset.sum_insert ht, Finset.erase_insert ht, hsum2, hct, Finset.sum_congr rfl hper, add_mul,
      one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_congr rfl hmul, add_smul, one_smul,
      Finset.sum_smul]
    simp only [Finset.sum_sub_distrib]
    abel

theorem inv_one_sub_C_mul_X (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X)⁻¹ = PowerSeries.mk (fun k => c ^ k) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, mul_comm (PowerSeries.mk _) (PowerSeries.C c), mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

theorem resSeries_eq_sum {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) :
    resSeries a = ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) •
      (PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) := by
  have hP : ∀ s, PowerSeries.constantCoeff (1 - PowerSeries.C (a s) * PowerSeries.X) ≠ 0 := by
    intro s; simp
  have h := prod_one_add_eq_of_resolvent (Finset.univ : Finset (Fin n)) (PowerSeries ℂ) a ha.injOn
    (fun s => PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) (fun s _ t _ _ => by
      have key : (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ - (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ =
          (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ *
            ((1 - PowerSeries.C (a s) * PowerSeries.X) - (1 - PowerSeries.C (a t) * PowerSeries.X)) := by
        rw [mul_sub, mul_assoc, PowerSeries.inv_mul_cancel _ (hP s), mul_one,
          mul_comm ((1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹), mul_assoc,
          PowerSeries.inv_mul_cancel _ (hP t), mul_one]
      rw [← mul_sub, key, PowerSeries.smul_eq_C_mul, map_sub]
      ring)
  rw [resSeries, h, add_sub_cancel_left]

theorem resSeries_coeff_succ' {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) =
      ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) * a s ^ k := by
  rw [resSeries_eq_sum ha, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [PowerSeries.coeff_smul, inv_one_sub_C_mul_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    smul_eq_mul]

theorem not_injective_shift_iff {μ ν : Fin n → ℝ} (hμ : Function.Injective μ) (s : Fin n) (c : ℝ)
    (hs : ν s = μ s + c) (ho : ∀ x, x ≠ s → ν x = μ x) :
    ¬ Function.Injective ν ↔ ∃ s' ∈ univ.erase s, μ s + c = μ s' := by
  constructor
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨x, y, hxy, hne⟩ := h
    by_cases hx : x = s
    · subst hx
      refine ⟨y, by simp [Ne.symm hne], ?_⟩
      rw [← hs, hxy, ho y (Ne.symm hne)]
    · by_cases hy : y = s
      · subst hy
        refine ⟨x, by simp [hx], ?_⟩
        rw [← hs, ← hxy, ho x hx]
      · exact absurd (hμ (by rw [← ho x hx, ← ho y hy, hxy])) hne
  · rintro ⟨s', hs', h⟩ hinj
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    exact hne (hinj (by rw [ho s' hne, hs, h]))

theorem resSeries_coeff_zero (a : Fin n → ℂ) : PowerSeries.coeff 0 (resSeries a) = 0 := by
  simp [resSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]

theorem resSeries_coeff_succ {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) = ∑ s, resid a s * a s ^ k := by
  rw [resSeries_coeff_succ' ha k]
  rfl

theorem resid_poleV (μ : Fin n → ℝ) (s : Fin n) : resid (poleV μ) s = ((ratioV μ s : ℝ) : ℂ) := by
  simp only [resid, ratioV, poleV]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  ring

theorem resid_poleVd (μ : Fin n → ℝ) (s : Fin n) : resid (poleVd μ) s = ((ratioVd μ s : ℝ) : ℂ) := by
  simp only [resid, ratioVd, poleVd]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  rw [← neg_div_neg_eq]
  ring

theorem poleV_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleV μ) := by
  intro x y h
  apply hμ
  simp only [poleV] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem poleVd_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleVd μ) := by
  intro x y h
  apply hμ
  simp only [poleVd] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem ratioV_nonneg {μ : Fin n → ℝ} (hμ : Function.Injective μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ))
    (s : Fin n) : 0 ≤ ratioV μ s ∧ (ratioV μ s = 0 ↔ ¬ Function.Injective (μ + Pi.single s 1)) := by
  have hfac : ∀ s' ∈ univ.erase s, 0 ≤ (μ s + 1 - μ s') / (μ s - μ s') := by
    intro s' hs'
    obtain ⟨m, hm⟩ := hint s s'
    rw [show μ s + 1 - μ s' = (μ s - μ s') + 1 by ring, hm]
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, sub_eq_zero] at hm
      exact (Finset.mem_erase.mp hs').1 (hμ hm).symm
    rcases lt_or_gt_of_ne hm0 with h | h
    · have h' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · have h' : (1 : ℝ) ≤ m := by exact_mod_cast h
      exact div_nonneg (by linarith) (by linarith)
  refine ⟨Finset.prod_nonneg hfac, ?_⟩
  rw [ratioV, Finset.prod_eq_zero_iff,
    not_injective_shift_iff hμ s 1 (by simp) (fun x hx => by simp [Pi.single_apply, hx])]
  refine exists_congr fun s' => and_congr_right fun hs' => ?_
  have hd : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hs').1 (hμ h).symm)
  rw [div_eq_zero_iff, or_iff_left hd, sub_eq_zero]

theorem ratioVd_nonneg {μ : Fin n → ℝ} (hμ : Function.Injective μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ))
    (s : Fin n) : 0 ≤ ratioVd μ s ∧ (ratioVd μ s = 0 ↔ ¬ Function.Injective (μ - Pi.single s 1)) := by
  have hfac : ∀ s' ∈ univ.erase s, 0 ≤ (μ s - 1 - μ s') / (μ s - μ s') := by
    intro s' hs'
    obtain ⟨m, hm⟩ := hint s s'
    rw [show μ s - 1 - μ s' = (μ s - μ s') - 1 by ring, hm]
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, sub_eq_zero] at hm
      exact (Finset.mem_erase.mp hs').1 (hμ hm).symm
    rcases lt_or_gt_of_ne hm0 with h | h
    · have h' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · have h' : (1 : ℝ) ≤ m := by exact_mod_cast h
      exact div_nonneg (by linarith) (by linarith)
  refine ⟨Finset.prod_nonneg hfac, ?_⟩
  rw [ratioVd, Finset.prod_eq_zero_iff,
    not_injective_shift_iff hμ s (-1) (by simp [sub_eq_add_neg])
      (fun x hx => by simp [Pi.single_apply, hx])]
  refine exists_congr fun s' => and_congr_right fun hs' => ?_
  have hd : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hs').1 (hμ h).symm)
  rw [div_eq_zero_iff, or_iff_left hd]
  constructor <;> intro h <;> linarith

theorem ratioVd_add_single_mul {μ : Fin n → ℝ} (s : Fin n) (hμ : Function.Injective μ)
    (hμs : Function.Injective (μ + Pi.single s 1)) :
    ratioVd (μ + Pi.single s 1) s * ratioV μ s = 1 := by
  rw [ratioVd, ratioV, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro s' hs'
  have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
  have h1 : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => hne (hμ h).symm)
  have h2 : μ s + 1 - μ s' ≠ 0 := by
    intro h
    apply hne
    apply hμs
    simp [Pi.single_apply, hne]
    linarith
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false, add_zero]
  rw [show μ s + 1 - 1 - μ s' = μ s - μ s' by ring]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
