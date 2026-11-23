import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaBounded
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem prefixLe_sub_of_coeff_near (n : ℕ) : ∀ {x x' : Γ} {B δ : ℝ}, 0 ≤ δ → δ ≤ B →
    T.PrefixLe x n B → T.PrefixLe x' n B → (∀ m ≤ n, ‖T.coeff x' m - T.coeff x m‖ ≤ δ) →
      T.PrefixLe (x' - x) n (B ^ (1 - coeffHolderExp p n) * δ ^ coeffHolderExp p n) := by
  induction n with
  | zero =>
    intro x x' B δ hδ hδB _ _ hd m hm
    obtain rfl : m = 0 := by omega
    rw [coeff_zero, map_sub]
    have := hd 0 le_rfl
    rw [coeff_zero, coeff_zero] at this
    exact this.trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one 0).2)
  | succ n ih =>
    intro x x' B δ hδ hδB hx hx' hd m hm
    obtain ⟨hs0, hs1⟩ := inv_pow_pos_le_one (p := p) (n + 1)
    set s := ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ with hsdef
    have hB0 : 0 ≤ B := hδ.trans hδB
    have hδ' : 0 ≤ B ^ (1 - s) * δ ^ s :=
      mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _)
    have hδδ' : δ ≤ B ^ (1 - s) * δ ^ s := le_rpow_mix hδ hδB hs1
    have hδ'B : B ^ (1 - s) * δ ^ s ≤ B := rpow_mix_le hδ hδB hs0.le hs1
    have hd0 : ‖T.red (x' - x)‖ ≤ δ := by
      have := hd 0 (Nat.zero_le _)
      rwa [coeff_zero, coeff_zero, ← map_sub] at this
    rcases m with _ | m
    · rw [coeff_zero]
      exact hd0.trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one _).2)
    set d := x' - x with hddef
    set H := T.teich (T.red x) + T.teich (T.red d) - T.teich (T.red x + T.red d) with hHdef
    have hH : T.red H = 0 := by rw [hHdef]; simp [red_teich]
    obtain ⟨h', hh'⟩ := T.red_eq_zero_iff.1 hH
    have htail : T.tail (x + d) = T.tail x + (T.tail d + h') := by
      refine T.tail_eq (a := T.red x + T.red d) ?_
      have ex := T.eq_teich_add_π_mul_tail x
      have ey := T.eq_teich_add_π_mul_tail d
      calc x + d = T.teich (T.red x) + T.π * T.tail x + (T.teich (T.red d) + T.π * T.tail d) := by
            rw [← ex, ← ey]
        _ = T.teich (T.red x + T.red d) + H + T.π * T.tail x + T.π * T.tail d := by
            rw [hHdef]; ring
        _ = _ := by rw [hh']; ring
    have hxd : x + d = x' := by rw [hddef]; ring
    rw [hxd] at htail
    have hHb : T.PrefixLe H (n + 1) (B ^ (1 - s) * δ ^ s) := by
      have := T.prefixLe_teich_add_sub_of_le (hx 0 (Nat.zero_le _)) hd0 hδ hδB (n + 1)
      have e : H = -(T.teich (T.red x + T.red d) - T.teich (T.red x) - T.teich (T.red d)) := by
        rw [hHdef]; ring
      rw [e]; exact T.prefixLe_neg this
    have hh'b : T.PrefixLe h' n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← T.coeff_π_mul_succ, ← hh']; exact hHb (i + 1) (by omega)
    have hxt : T.PrefixLe (T.tail x) n B := fun i hi => by
      rw [← coeff_succ]; exact hx (i + 1) (by omega)
    have hx't : T.PrefixLe (T.tail x') n B := fun i hi => by
      rw [← coeff_succ]; exact hx' (i + 1) (by omega)
    have hdt : ∀ i ≤ n, ‖T.coeff (T.tail x') i - T.coeff (T.tail x) i‖ ≤ B ^ (1 - s) * δ ^ s :=
      fun i hi => by rw [← coeff_succ, ← coeff_succ]; exact (hd (i + 1) (by omega)).trans hδδ'
    have hI := ih hδ' hδ'B hxt hx't hdt
    have htd : T.tail d = (T.tail x' - T.tail x) - h' := by rw [htail]; ring
    have hmix : B ^ (1 - s) * δ ^ s ≤
        B ^ (1 - coeffHolderExp p n) * (B ^ (1 - s) * δ ^ s) ^ coeffHolderExp p n :=
      le_rpow_mix hδ' hδ'B (coeffHolderExp_pos_le_one n).2
    have hfin := T.prefixLe_sub hI (hh'b.mono hmix)
    rw [coeff_succ, htd]
    refine (hfin m (by omega)).trans (le_of_eq ?_)
    obtain ⟨ht0, ht1⟩ := coeffHolderExp_pos_le_one (p := p) n
    have hne : 1 - coeffHolderExp p n + (1 - s) * coeffHolderExp p n ≠ 0 := by
      have : s * coeffHolderExp p n ≤ s := mul_le_of_le_one_right hs0.le ht1
      have hs2 : s < 1 := by
        rw [hsdef]
        have h2 : (1 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_lt_pow (by omega) hp.out.one_lt
        exact inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _), ← Real.rpow_mul hB0,
      ← Real.rpow_mul hδ, ← mul_assoc, ← Real.rpow_add' hB0 hne, coeffHolderExp_succ]
    congr 2 <;> ring

theorem exists_holder_lt {B t ε : ℝ} (hB : 0 < B) (ht : 0 < t) (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ B ∧ ∀ δ', 0 ≤ δ' → δ' ≤ δ → B ^ (1 - t) * δ' ^ t < ε := by
  have hBt : 0 < B ^ (1 - t) := Real.rpow_pos_of_pos hB _
  set c := ε / (2 * B ^ (1 - t)) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨min B (c ^ t⁻¹), lt_min hB (Real.rpow_pos_of_pos hc0 _), min_le_left _ _,
    fun δ' h0 h1 => ?_⟩
  have h2 : δ' ^ t ≤ c := by
    calc δ' ^ t ≤ (c ^ t⁻¹) ^ t := Real.rpow_le_rpow h0 (h1.trans (min_le_right _ _)) ht.le
      _ = c := Real.rpow_inv_rpow hc0.le ht.ne'
  calc B ^ (1 - t) * δ' ^ t ≤ B ^ (1 - t) * c := mul_le_mul_of_nonneg_left h2 hBt.le
    _ = ε / 2 := by rw [hc]; field_simp
    _ < ε := by linarith

theorem tendsto_coeff_add {ι : Type*} {l : Filter ι} (z : Γ) {w : ι → Γ} (n : ℕ)
    (hw : ∀ δ > 0, ∀ᶠ i in l, T.PrefixLe (w i) n δ) :
    Tendsto (fun i => T.coeff (z + w i) n) l (𝓝 (T.coeff z n)) := by
  obtain ⟨B0, hB0, -⟩ := T.exists_prefix_max z n
  set B : ℝ := ‖B0‖ + 1 with hBdef
  have hB : 0 < B := by positivity
  have hzB : T.PrefixLe z n B := hB0.mono (by rw [hBdef]; linarith)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) n).1 hε
  filter_upwards [hw δ hδ0] with i hi
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (T.norm_coeff_add_sub_le n hδ0.le hδB hzB hi n le_rfl) (hδ δ hδ0.le le_rfl)

variable [CompleteSpace L]

def coeffLim (x : ℕ → Γ) : Γ := T.ofCoeff fun m => limUnder atTop fun k => T.coeff (x k) m

theorem tendsto_coeff_coeffLim {x : ℕ → Γ} (h : ∀ m, CauchySeq fun k => T.coeff (x k) m)
    (m : ℕ) : Tendsto (fun k => T.coeff (x k) m) atTop (𝓝 (T.coeff (T.coeffLim x) m)) := by
  rw [coeffLim, coeff_ofCoeff]; exact (h m).tendsto_limUnder

theorem prefixLe_sub_coeffLim {x : ℕ → Γ} (h : ∀ m, CauchySeq fun k => T.coeff (x k) m)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, T.PrefixLe (x k - T.coeffLim x) n ε := by
  set y := T.coeffLim x
  set B := 1 + ∑ m ∈ Finset.range (n + 1), ‖T.coeff y m‖ with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]; linarith [Finset.sum_nonneg fun m (_ : m ∈ Finset.range (n + 1)) =>
      norm_nonneg (T.coeff y m)]
  have hB : 0 < B := by linarith
  have hyB : ∀ m ≤ n, ‖T.coeff y m‖ + 1 ≤ B := fun m hm => by
    rw [hBdef, add_comm]
    exact add_le_add_right (Finset.single_le_sum (f := fun m => ‖T.coeff y m‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))) 1
  obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) n).1 hε
  set δ1 := min δ 1 with hδ1
  have hδ10 : 0 < δ1 := lt_min hδ0 one_pos
  have hev : ∀ᶠ k in atTop, ∀ m ∈ Finset.range (n + 1), ‖T.coeff (x k) m - T.coeff y m‖ < δ1 := by
    rw [Filter.eventually_all_finset]
    intro m _
    have := (T.tendsto_coeff_coeffLim h m)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this δ1 hδ10] with k hk
    rwa [dist_eq_norm] at hk
  filter_upwards [hev] with k hk
  have hk' : ∀ m ≤ n, ‖T.coeff (x k) m - T.coeff y m‖ ≤ δ1 := fun m hm =>
    (hk m (Finset.mem_range.2 (by omega))).le
  have hxB : T.PrefixLe (x k) n B := fun m hm => by
    have h1 : ‖T.coeff (x k) m‖ ≤ ‖T.coeff (x k) m - T.coeff y m‖ + ‖T.coeff y m‖ := by
      calc ‖T.coeff (x k) m‖ = ‖(T.coeff (x k) m - T.coeff y m) + T.coeff y m‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 := hk' m hm
    have h3 := hyB m hm
    have h4 : δ1 ≤ 1 := min_le_right _ _
    linarith
  have hyB' : T.PrefixLe y n B := fun m hm => by linarith [hyB m hm]
  have hδ1B : δ1 ≤ B := (min_le_right _ _).trans hB1
  have := T.prefixLe_sub_of_coeff_near n hδ10.le hδ1B hyB' hxB hk'
  exact this.mono (hδ δ1 hδ10.le (min_le_left _ _)).le

omit [CompleteSpace L] in
theorem convergesAt_zcoeff_sub {x y : Γ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    ConvergesAt (T.zcoeff (x - y)) ρ := by
  rw [sub_eq_add_neg]
  exact T.convergesAt_zcoeff_add hρ0 hρ1 hx (T.convergesAt_zcoeff_neg hρ0 hρ1 hy)

omit [CompleteSpace L] in

theorem prefixLe_of_weight {y : Γ} {ρ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : ∀ m : ℕ, ‖T.coeff y m‖ * ρ ^ m ≤ M) (j : ℕ) : T.PrefixLe y j (M / ρ ^ j) := by
  intro m hm
  have := norm_le_div_of_weight (a := T.coeff y m) (m := (m : ℤ)) (n := (j : ℤ)) hρ0 hρ1
    (M := M) (by exact_mod_cast hm) (by rw [zpow_natCast]; exact h m)
  rwa [zpow_natCast] at this

theorem exists_limit_gaussNorm {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : ℕ → Γ}
    (hx : ∀ k, ConvergesAt (T.zcoeff (x k)) ρ)
    (hc : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, gaussNorm (T.zcoeff (x k - x l)) ρ ≤ ε) :
    (∀ m, CauchySeq fun k => T.coeff (x k) m) ∧ ConvergesAt (T.zcoeff (T.coeffLim x)) ρ ∧
      ∀ ε > 0, ∃ N, ∀ k ≥ N, gaussNorm (T.zcoeff (x k - T.coeffLim x)) ρ ≤ ε := by
  have hsub : ∀ k l, ConvergesAt (T.zcoeff (x k - x l)) ρ := fun k l =>
    T.convergesAt_zcoeff_sub hρ0 hρ1 (hx k) (hx l)
  have hw : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ j : ℕ, ‖T.coeff (x k - x l) j‖ * ρ ^ j ≤ ε := by
    intro ε hε; obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun k hk l hl j => ?_⟩
    have := (hsub k l).le_gaussNorm j
    rw [zcoeff_natCast, zpow_natCast] at this
    exact this.trans (hN k hk l hl)
  obtain ⟨N1, hN1⟩ := hw 1 one_pos
  set C := max (gaussNorm (T.zcoeff (x N1)) ρ) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hbd : ∀ k ≥ N1, ∀ j : ℕ, T.PrefixLe (x k) j (C / ρ ^ j) := by
    intro k hk j m hm
    have e : x k = x N1 + (x k - x N1) := by ring
    have hb : 0 ≤ C / (ρ ^ (j : ℤ)) := div_nonneg (by linarith) (zpow_pos hρ0 _).le
    have := T.norm_zcoeff_add_le (x := x N1) (y := x k - x N1) (n := (m : ℤ)) hb
      (fun i hi => norm_le_div_of_weight hρ0 hρ1.le (hi.trans (by exact_mod_cast hm))
        (((hx N1).le_gaussNorm i).trans (le_max_left _ _)))
      (fun i hi => by
        rcases lt_or_ge i 0 with hi0 | hi0
        · rw [T.zcoeff_of_neg _ hi0, norm_zero]; exact hb
        · lift i to ℕ using hi0
          refine norm_le_div_of_weight hρ0 hρ1.le (hi.trans (by exact_mod_cast hm)) ?_
          rw [zcoeff_natCast, zpow_natCast]
          exact (hN1 k hk N1 le_rfl i).trans hC1)
    rw [← e, zcoeff_natCast] at this
    rwa [zpow_natCast] at this
  have hcoeff : ∀ m, CauchySeq fun k => T.coeff (x k) m := by
    intro m
    rw [Metric.cauchySeq_iff]
    intro ε' hε'
    have hB : 0 < C / ρ ^ m := div_pos (by linarith) (pow_pos hρ0 m)
    obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) m).1 hε'
    obtain ⟨N, hN⟩ := hw (δ * ρ ^ m) (mul_pos hδ0 (pow_pos hρ0 m))
    refine ⟨max N1 N, fun k hk l hl => ?_⟩
    have hk1 : N1 ≤ k := le_of_max_le_left hk
    have hkN : N ≤ k := le_of_max_le_right hk
    have hl1 : N1 ≤ l := le_of_max_le_left hl
    have hlN : N ≤ l := le_of_max_le_right hl
    have hyδ : T.PrefixLe (x k - x l) m δ := by
      have := T.prefixLe_of_weight hρ0 hρ1.le (hN k hkN l hlN) m
      rwa [mul_div_assoc, div_self (pow_pos hρ0 m).ne', mul_one] at this
    have := T.norm_coeff_add_sub_le m hδ0.le hδB (hbd l hl1 m) hyδ m le_rfl
    rw [show x l + (x k - x l) = x k by ring] at this
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (hδ δ hδ0.le le_rfl)
  refine ⟨hcoeff, ?_⟩
  set y := T.coeffLim x

  have hwy : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ j : ℕ, ‖T.coeff (x k - y) j‖ * ρ ^ j ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hw ε hε
    refine ⟨N, fun k hk j => ?_⟩
    have ht : Tendsto (fun l => T.coeff ((x k - y) + (y - x l)) j) atTop
        (𝓝 (T.coeff (x k - y) j)) := by
      refine T.tendsto_coeff_add (x k - y) j fun δ hδ => ?_
      filter_upwards [T.prefixLe_sub_coeffLim hcoeff j hδ] with l hl
      rw [← neg_sub]; exact T.prefixLe_neg hl
    have ht' := (ht.norm).mul_const (ρ ^ j)
    refine le_of_tendsto ht' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with l hl
    rw [show x k - y + (y - x l) = x k - x l by ring]
    exact hN k hk l hl j
  have hwy' : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ j : ℤ, ‖T.zcoeff (x k - y) j‖ * ρ ^ j ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hwy ε hε
    refine ⟨N, fun k hk j => ?_⟩
    rcases lt_or_ge j 0 with hj | hj
    · rw [T.zcoeff_of_neg _ hj, norm_zero, zero_mul]; exact hε.le
    · lift j to ℕ using hj
      rw [zcoeff_natCast, zpow_natCast]; exact hN k hk j
  have hyconv : ConvergesAt (T.zcoeff y) ρ := by
    refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
    obtain ⟨N, hN⟩ := hwy' ε hε
    obtain ⟨N', hN'⟩ := exists_prefix_small hρ0 hρ1 (hx N) hε
    refine ⟨N', fun n hn => ?_⟩
    have hb : 0 ≤ ε / ρ ^ n := div_nonneg hε.le (zpow_pos hρ0 n).le
    have := T.norm_zcoeff_add_le (x := x N) (y := -(x N - y)) (n := n) hb
      (fun m hm => by rw [le_div_iff₀ (zpow_pos hρ0 n)]; exact hN' n hn m hm)
      (fun m hm => T.norm_zcoeff_neg_le hb fun i hi =>
        norm_le_div_of_weight hρ0 hρ1.le (hi.trans hm) (hN N le_rfl i))
    rw [show x N + -(x N - y) = y by ring, le_div_iff₀ (zpow_pos hρ0 n)] at this
    exact this
  refine ⟨hyconv, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hwy' ε hε
  exact ⟨N, fun k hk => gaussNorm_le fun j => hN k hk j⟩

end TeichLift

end GroundTheory.PAdicHodge
