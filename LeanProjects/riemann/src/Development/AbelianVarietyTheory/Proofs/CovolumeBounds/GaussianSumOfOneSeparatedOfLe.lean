import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated

open Metric MeasureTheory Module Set Real

namespace GlobalTheory

theorem finset_sum_exp_neg_le_of_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by
  have hint : IntegrableOn (fun u : ℝ => exp (-u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi t)
  have h1 : ∀ i ∈ s, exp (-f i) =
      ∫ u in Ici t, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, sup_eq_right.2 (hf i hi),
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
  have hint2 : IntegrableOn (fun u : ℝ => exp (-(1 / 2) * u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi t (by norm_num))
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _
    (fun i _ => hint.indicator measurableSet_Ici)]
  calc ∫ u in Ici t, ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u
      ≤ ∫ u in Ici t, (C * exp (-t / 2)) * exp (-(1 / 2) * u) := by
        refine setIntegral_mono_on
          (integrable_finset_sum _ fun i _ => hint.indicator measurableSet_Ici)
          (hint2.const_mul _) measurableSet_Ici fun u hu => ?_
        have e : ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u =
            ((s.filter fun i => f i ≤ u).card : ℝ) * exp (-u) := by
          simp only [indicator, mem_Ici]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [e]
        calc _ ≤ C * exp ((u - t) / 2) * exp (-u) :=
              mul_le_mul_of_nonneg_right (hc u hu) (exp_pos _).le
          _ = _ := by
              rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]; congr 2; ring
    _ = 2 * C * exp (-t) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
          integral_exp_mul_Ioi (by norm_num)]
        have : exp (-t) = exp (-t / 2) * exp (-(1 / 2) * t) := by
          rw [← exp_add]; congr 1; ring
        rw [this]; ring

theorem summable_exp_neg_of_card_le {ι : Type*} (f : ι → ℝ) {t C : ℝ} (hf : ∀ i, t ≤ f i)
    (hc : ∀ (s : Finset ι) u, t ≤ u → (∀ i ∈ s, f i ≤ u) → (s.card : ℝ) ≤ C * exp ((u - t) / 2)) :
    Summable (fun i => exp (-f i)) ∧ ∑' i, exp (-f i) ≤ 2 * C * exp (-t) := by
  have key : ∀ s : Finset ι, ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := fun s =>
    finset_sum_exp_neg_le_of_card_le s f (fun i _ => hf i) fun u hu =>
      hc _ u hu fun i hi => (Finset.mem_filter.1 hi).2
  have hs := summable_of_sum_le (fun i => (exp_pos (-f i)).le) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finset_card_le_of_separated_family {ι : Type*} (u : ι → E) {r R : ℝ} (hr : 0 < r)
    (hR : 0 ≤ R) (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (w : E) (s : Finset ι)
    (hs : ∀ i ∈ s, dist (u i) w ≤ R) : (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ E := by
  classical
  have hinj : Function.Injective u := fun i j hij => by
    by_contra hne
    have := hu hne
    simp only [hij, dist_self] at this
    linarith
  rw [← Finset.card_image_of_injective s hinj]
  refine finset_card_le_of_separated _ hr hR w ?_ ?_
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    exact hs i hi
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hu fun h => hab (h ▸ rfl)

theorem gaussian_tail_of_separated {ι : Type*} (u : ι → E) (w : E) {r q : ℝ} (hr : 0 < r)
    (hq : 0 < q) (hd : (finrank ℝ E : ℝ) ≤ q * r ^ 2)
    (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (hw : ∀ i, r ≤ ‖u i - w‖) :
    Summable (fun i => exp (-(q * ‖u i - w‖ ^ 2))) ∧
      ∑' i, exp (-(q * ‖u i - w‖ ^ 2)) ≤ 2 * 3 ^ finrank ℝ E * exp (-(q * r ^ 2)) := by
  refine summable_exp_neg_of_card_le (fun i => q * ‖u i - w‖ ^ 2) (fun i => ?_) ?_
  · have := hw i
    gcongr
  · intro s v hv hs
    have ht : 0 < q * r ^ 2 := by positivity
    have hv0 : 0 < v := ht.trans_le hv
    set R := √(v / q) with hRdef
    have hR0 : 0 ≤ R := sqrt_nonneg _
    have hR2 : R ^ 2 = v / q := sq_sqrt (by positivity)
    have hcard := finset_card_le_of_separated_family u hr hR0 hu w s fun i hi => by
      rw [dist_eq_norm]
      refine le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hq, mul_comm]
      exact hs i hi
    refine hcard.trans ?_
    set x := R / r with hx
    have hx0 : 0 ≤ x := by positivity
    have hx2 : x ^ 2 = v / (q * r ^ 2) := by rw [hx, div_pow, hR2]; field_simp
    have hx1 : 1 ≤ x ^ 2 := by rw [hx2]; exact (one_le_div ht).2 hv
    have h1 : 1 + 2 * R / r ≤ 3 * exp ((x ^ 2 - 1) / 2) := by
      have := add_one_le_exp ((x ^ 2 - 1) / 2)
      rw [mul_div_assoc, ← hx]
      nlinarith [sq_nonneg (x - 1)]
    calc (1 + 2 * R / r) ^ finrank ℝ E ≤ (3 * exp ((x ^ 2 - 1) / 2)) ^ finrank ℝ E :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = 3 ^ finrank ℝ E * exp ((finrank ℝ E : ℝ) * ((x ^ 2 - 1) / 2)) := by
          rw [mul_pow, exp_nat_mul]
      _ ≤ 3 ^ finrank ℝ E * exp (q * r ^ 2 * ((x ^ 2 - 1) / 2)) := by
          gcongr
      _ = _ := by rw [hx2]; congr 2; field_simp

theorem gaussian_tail_addMonoidHom {A : Type*} [AddGroup A] (u : A →+ E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hu : ∀ y, y ≠ 0 → b ≤ ‖u y‖ ^ 2) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-(q * ‖u y‖ ^ 2))) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-(q * ‖u y‖ ^ 2)) ≤ 2 * 3 ^ finrank ℝ E * exp (-(q * b)) := by
  have hq : 0 < q := by
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    exact (mul_pos_iff_of_pos_right hb).1 (by linarith)
  have hb2 : √b ^ 2 = b := sq_sqrt hb.le
  have hu' : ∀ y, y ≠ 0 → √b ≤ ‖u y‖ := fun y hy => sqrt_le_iff.2 ⟨norm_nonneg _, hu y hy⟩
  have := gaussian_tail_of_separated (fun y : {y : A // y ≠ 0} => u y) 0 (sqrt_pos.2 hb) hq
    (by rw [hb2]; linarith)
    (fun i j hij => by
      change √b ≤ dist (u i) (u j)
      rw [dist_eq_norm, ← map_sub]
      exact hu' _ (sub_ne_zero.2 fun h => hij (Subtype.ext h)))
    (fun i => by rw [sub_zero]; exact hu' _ i.2)
  simpa only [sub_zero, hb2] using this

theorem gaussian_tail_sum_le_of_min_norm_sq {A : Type*} [AddGroup A] (u : A →+ E) {b q : ℝ}
    (hb : 0 < b) (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hu : ∀ y, y ≠ 0 → b ≤ ‖u y‖ ^ 2) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-(q * ‖u y‖ ^ 2))) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-(q * ‖u y‖ ^ 2)) ≤
        2 * 4.3 ^ finrank ℝ E * exp (-(q * b)) := by
  have h := gaussian_tail_addMonoidHom u hb hd hu
  refine ⟨h.1, h.2.trans ?_⟩
  gcongr; norm_num

theorem gaussian_tail_addMonoidHom_sixteen {A : Type*} [AddGroup A] (u : A →+ E) {g : ℕ}
    (hg : finrank ℝ E = 2 * g) {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hu : ∀ y, y ≠ 0 → R ≤ ‖u y‖) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-‖u y‖ ^ 2 / 16)) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-‖u y‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have h := gaussian_tail_addMonoidHom u (b := R ^ 2) (q := 1 / 16) (by linarith)
    (by rw [hg]; push_cast; linarith) (fun y hy => by have := hu y hy; gcongr)
  have e : ∀ x : ℝ, -(1 / 16 * x) = -x / 16 := fun x => by ring
  simp only [e] at h
  rw [hg, pow_mul] at h
  norm_num at h ⊢
  exact h

theorem gaussian_sum_of_one_separated {ι : Type*} (u : ι → E) (w : E) (hd : 1 ≤ finrank ℝ E)
    (hu : Pairwise fun i j => 1 ≤ dist (u i) (u j)) :
    Summable (fun i => exp (-(π / 2 * ‖w - u i‖ ^ 2))) ∧
      ∑' i, exp (-(π / 2 * ‖w - u i‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E := by
  have h := summable_exp_neg_of_card_le (fun i => π / 2 * ‖w - u i‖ ^ 2) (t := 0)
    (C := (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) (fun i => by positivity) ?_
  · simpa only [neg_zero, exp_zero, mul_one] using h
  intro s v hv hs
  have hq : 0 < π / 2 := by positivity
  set R := √(v / (π / 2)) with hRdef
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = v / (π / 2) := sq_sqrt (by positivity)
  have hv2 : v = π / 2 * R ^ 2 := by rw [hR2]; field_simp
  have hcard := finset_card_le_of_separated_family u one_pos hR0 hu w s fun i hi => by
    rw [dist_comm, dist_eq_norm]
    refine le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hq, mul_comm]
    exact hs i hi
  refine hcard.trans ?_
  set d := finrank ℝ E
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 1 + 2 * R / 1 ≤ 3 * (d : ℝ) * exp (v / (2 * d)) := by
    have h2 := add_one_le_exp (v / (2 * d))
    have h3 : 3 * (d : ℝ) * (v / (2 * d) + 1) = 3 / 2 * v + 3 * d := by field_simp
    have h4 : 3 * (d : ℝ) * (v / (2 * d) + 1) ≤ 3 * (d : ℝ) * exp (v / (2 * d)) := by gcongr
    have h5 : 3 / 2 * R ^ 2 ≤ v := by
      rw [hv2]; have := pi_gt_three; gcongr
    nlinarith [sq_nonneg (R - 1)]
  calc (1 + 2 * R / 1) ^ d ≤ (3 * (d : ℝ) * exp (v / (2 * d))) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = _ := by
        rw [mul_pow, ← exp_nat_mul]; congr 2; field_simp; ring

theorem gaussian_sum_of_one_separated_of_le {ι : Type*} (u : ι → E) (w : E)
    (hd : 1 ≤ finrank ℝ E) (hu : Pairwise fun i j => 1 ≤ dist (u i) (u j)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ i, ρ ≤ ‖w - u i‖) :
    Summable (fun i => exp (-(π * ‖w - u i‖ ^ 2))) ∧
      ∑' i, exp (-(π * ‖w - u i‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * ρ ^ 2)) := by
  obtain ⟨hs, hb⟩ := gaussian_sum_of_one_separated u w hd hu
  have hle : ∀ i, exp (-(π * ‖w - u i‖ ^ 2)) ≤
      exp (-(π / 2 * ‖w - u i‖ ^ 2)) * exp (-(π / 2 * ρ ^ 2)) := fun i => by
    rw [← exp_add, exp_le_exp]
    have h1 : π / 2 * ρ ^ 2 ≤ π / 2 * ‖w - u i‖ ^ 2 := by have := hw i; gcongr
    linarith
  have hs2 := hs.mul_right (exp (-(π / 2 * ρ ^ 2)))
  have hs1 := Summable.of_nonneg_of_le (fun i => (exp_pos _).le) hle hs2
  refine ⟨hs1, (hs1.tsum_le_tsum hle hs2).trans ?_⟩
  rw [tsum_mul_right]
  gcongr

theorem subgroup_gaussian_tail_sixteen (G : AddSubgroup E) {g : ℕ} (hg : finrank ℝ E = 2 * g)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hG : ∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) :
    Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
      ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) :=
  gaussian_tail_addMonoidHom_sixteen G.subtype hg hR0 hR fun y hy =>
    hG y y.2 fun h => hy (Subtype.ext h)

theorem subgroup_gaussian_tail (G : AddSubgroup E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hG : ∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) :
    Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
      ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
        2 * 3 ^ finrank ℝ E * exp (-(q * b)) :=
  gaussian_tail_addMonoidHom G.subtype hb hd fun y hy => hG y y.2 fun h => hy (Subtype.ext h)

theorem subgroup_gaussian_tail_dyadic (G : AddSubgroup E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hG : ∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) :
    Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
      ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
        2 * 4.3 ^ finrank ℝ E * exp (-(q * b)) :=
  gaussian_tail_sum_le_of_min_norm_sq G.subtype hb hd fun y hy =>
    hG y y.2 fun h => hy (Subtype.ext h)

theorem set_gaussian_sum_of_one_separated {S : Set E} (w : E) (hd : 1 ≤ finrank ℝ E)
    (hS : S.Pairwise fun a b => 1 ≤ dist a b) :
    (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
    (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2))) := by
  have hu : Pairwise fun i j : S => 1 ≤ dist (i : E) (j : E) := fun i j hij =>
    hS i.2 j.2 fun h => hij (Subtype.ext h)
  exact ⟨gaussian_sum_of_one_separated Subtype.val w hd hu,
    gaussian_sum_of_one_separated_of_le Subtype.val w hd hu infDist_nonneg fun i => by
      rw [← dist_eq_norm]; exact infDist_le_dist_of_mem i.2⟩

theorem gaussian_tail_sums :
    (∀ (G : AddSubgroup E) (g : ℕ) (R : ℝ), finrank ℝ E = 2 * g → 0 ≤ R →
      16 * (2 * (g : ℝ) + 1) ≤ R ^ 2 → (∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) →
      Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
        ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16)) ∧
    (∀ (S : Set E) (w : E), 1 ≤ finrank ℝ E → (S.Pairwise fun a b => 1 ≤ dist a b) →
      (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
      (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
          2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2)))) ∧
    (∀ (G : AddSubgroup E) (b q : ℝ), 0 < b → (finrank ℝ E : ℝ) + 1 ≤ q * b →
      (∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) →
      Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
        ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
          2 * 4.3 ^ finrank ℝ E * exp (-(q * b))) :=
  ⟨fun G _ _ hg hR0 hR hG => subgroup_gaussian_tail_sixteen G hg hR0 hR hG,
    fun _ w hd hS => set_gaussian_sum_of_one_separated w hd hS,
    fun G _ _ hb hd hG => subgroup_gaussian_tail_dyadic G hb hd hG⟩

end GlobalTheory
