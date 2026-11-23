import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermLat

section Lat

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem exists_smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  have hS0 : 0 ≤ ∑ i, ‖b.repr v i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L
    (show (0 : ℝ) < 1 / (1 + ∑ i, ‖b.repr v i‖) by positivity)
  refine ⟨a, norm_pos_iff.mp ha0, (hb _).2 fun i => ?_⟩
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr v i‖ ≤ 1 + ∑ i, ‖b.repr v i‖ := by
    have := Finset.single_le_sum (f := fun i => ‖b.repr v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc ‖a‖ * ‖b.repr v i‖ ≤ (1 / (1 + ∑ i, ‖b.repr v i‖)) * (1 + ∑ i, ‖b.repr v i‖) := by
        gcongr
    _ = 1 := by field_simp

variable (L) in

def adjoin [IsUltrametricDist L] (Λ : AddSubgroup V) (v : V) : AddSubgroup V where
  carrier := {z | ∃ l ∈ Λ, ∃ a : L, ‖a‖ ≤ 1 ∧ z = l + a • v}
  add_mem' := by
    rintro _ _ ⟨l, hl, a, ha, rfl⟩ ⟨l', hl', a', ha', rfl⟩
    refine ⟨l + l', Λ.add_mem hl hl', a + a',
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ha'), ?_⟩
    rw [add_smul]
    abel
  zero_mem' := ⟨0, Λ.zero_mem, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨l, hl, a, ha, rfl⟩
    refine ⟨-l, Λ.neg_mem hl, -a, by simpa using ha, ?_⟩
    rw [neg_smul]
    abel

end Lat

section Herm

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

theorem herm_add_add (hh : IsHerm s h) (u v : V) :
    h (u + v) (u + v) = h u u + (h u v + s (h u v)) + h v v := by
  rw [herm_add_left hh, hh.1, hh.1, ← hh.2.2.1 u v]
  ring

end Herm

section Main

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem norm_sub_le_of_le {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by simpa using hb))

theorem pairing_le (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 _).1 fun t ht => ?_
  have hty : t • y ∈ Λ := smul_mem_of_isLat hL ht hy
  have e := herm_add_add hh x (t • y)
  have e' : h x y * t + s (h x y * t) =
      h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e, hh.2.1 t x y, mul_comm t]
    ring
  rw [e']
  exact norm_sub_le_of_le (norm_sub_le_of_le (hint _ (Λ.add_mem hx hty)) (hint _ hx)) (hint _ hty)

theorem adjoin_integral (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin L Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by
  rintro _ ⟨l, hl, a, ha, rfl⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  rw [herm_add_add hh]
  have hb : ‖h l (a • p⁻¹ • x)‖ ≤ ‖δ‖ := by
    rw [hh.2.1, hh.2.1, hh.2.2.1 x l, norm_mul, norm_mul, norm_inv, hs.2.1]
    have h1 := hsmall l hl
    calc ‖a‖ * (‖p‖⁻¹ * ‖h x l‖) ≤ 1 * (‖p‖⁻¹ * (‖p‖ * ‖δ‖)) := by gcongr
      _ = ‖δ‖ := by field_simp
  have htr : ‖h l (a • p⁻¹ • x) + s (h l (a • p⁻¹ • x))‖ ≤ 1 := by
    have := (hδ.2.1 _).2 hb 1 (by simp)
    simpa using this
  have hlast : ‖h (a • p⁻¹ • x) (a • p⁻¹ • x)‖ ≤ 1 := by
    rw [herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1, norm_mul, norm_mul, norm_mul,
      norm_mul, hs.2.1, hs.2.1, norm_inv]
    have hpp : ‖p‖⁻¹ * (‖p‖⁻¹ * ‖p‖ ^ 2) = 1 := by field_simp
    calc ‖a‖ * (‖p‖⁻¹ * (‖a‖ * (‖p‖⁻¹ * ‖h x x‖)))
        ≤ 1 * (‖p‖⁻¹ * (1 * (‖p‖⁻¹ * ‖p‖ ^ 2))) := by gcongr
      _ = 1 := by rw [one_mul, one_mul, hpp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint l hl) htr)) hlast)

theorem pairing_of_sandwich : StSandwich → StPairing := by
  intro hS L _ _ _ _ s hs δ hδ V _ _ _ h hh Λ hΛ
  obtain ⟨hL, hint, hmax⟩ := hΛ
  refine ⟨fun x hx y hy => pairing_le hδ hh hL hint hx hy, ?_⟩
  intro p hp hunif x hx hxp hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 by norm_num)
    have := hunif a ha
    rw [norm_zero] at this
    linarith
  have hδ0 : δ ≠ 0 := hδ.1
  have hδn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  by_cases hex : ∃ y ∈ Λ, ‖h x y‖ = ‖δ‖
  · obtain ⟨y, hy, hyn⟩ := hex
    have hne : h x y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyn
      exact hδ0 (norm_eq_zero.mp hyn.symm)
    refine ⟨(δ / h x y) • y, smul_mem_of_isLat hL ?_ hy, ?_⟩
    · rw [norm_div, hyn, div_self hδn.ne']
    · rw [hh.2.1]
      field_simp
  · exfalso
    have hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖ := by
      intro y hy
      have hlt : ‖h x y‖ < ‖δ‖ :=
        lt_of_le_of_ne (pairing_le hδ hh hL hint hx hy) fun e => hex ⟨y, hy, e⟩
      have h2 : ‖h x y / δ‖ < 1 := by
        rw [norm_div, div_lt_one hδn]
        exact hlt
      have h3 := hunif _ h2
      rw [norm_div, div_le_iff₀ hδn] at h3
      exact h3
    have hle : Λ ≤ adjoin L Λ (p⁻¹ • x) := fun l hl => ⟨l, hl, 0, by simp, by simp⟩
    have hL' : IsLat L (adjoin L Λ (p⁻¹ • x)) := by
      refine hS L V Λ _ p hL hp0 ?_ ?_ ?_
      · rintro _ ⟨l, hl, a, ha, rfl⟩
        have e : p • (l + a • p⁻¹ • x) = p • l + a • x := by
          rw [smul_add, smul_comm p a, smul_smul p, mul_inv_cancel₀ hp0, one_smul]
        rw [e]
        exact Λ.add_mem (smul_mem_of_isLat hL hp.le hl) (smul_mem_of_isLat hL ha hx)
      · intro v
        obtain ⟨a, ha, hav⟩ := exists_smul_mem_of_isLat hL v
        exact ⟨a, ha, hle hav⟩
      · rintro b hb _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨b • l, smul_mem_of_isLat hL hb hl, b * a, ?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_one₀ hb (norm_nonneg _) ha
        · rw [smul_add, smul_smul]
    have heq := hmax _ hL' (adjoin_integral hs hδ hh hint hp0 hq hsmall) hle
    apply hxp
    rw [← heq]
    exact ⟨0, Λ.zero_mem, 1, by simp, by simp⟩

end Main

end GlobalTheory.CompanionTheory.HermLat

end
