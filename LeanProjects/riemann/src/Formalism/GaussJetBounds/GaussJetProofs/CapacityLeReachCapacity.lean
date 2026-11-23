import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementA
import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem asmA_odd_hasSum (l : ℕ) (hl : 2 ≤ l) :
    HasSum (fun e : ℕ => if Odd e then ((l : ℝ) ^ e)⁻¹ else 0) (gam l) := by
  have hl0 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  set r : ℝ := ((l : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl0 (by norm_num))
  have hg : HasSum (fun k : ℕ => (l : ℝ)⁻¹ * r ^ k) ((l : ℝ)⁻¹ * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have hval : (l : ℝ)⁻¹ * (1 - r)⁻¹ = gam l := by
    rw [gam, hr]
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (l : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hval] at hg
  have hodd : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simpa using h
  rw [← hodd.hasSum_iff]
  · convert hg using 1
    funext k
    have ho : Odd (2 * k + 1) := odd_two_mul_add_one k
    simp only [Function.comp, ho, if_true, hr]
    rw [pow_succ, pow_mul, mul_inv, mul_comm, inv_pow]
  · intro x hx
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hx ⟨k, rfl⟩

theorem asmA_sum_odd_le (l : ℕ) (hl : 2 ≤ l) (N : Finset ℕ) (hN : ∀ n ∈ N, Odd n) :
    ∑ n ∈ N, ((l : ℝ) ^ n)⁻¹ ≤ gam l := by
  calc ∑ n ∈ N, ((l : ℝ) ^ n)⁻¹
      = ∑ n ∈ N, (if Odd n then ((l : ℝ) ^ n)⁻¹ else 0) :=
        Finset.sum_congr rfl fun n hn => by rw [if_pos (hN n hn)]
    _ ≤ gam l := sum_le_hasSum N (fun i _ => by split_ifs <;> positivity) (asmA_odd_hasSum l hl)

theorem asmA_top_core (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (T : ℕ)
    (hT : A / (l : ℝ) ^ T ≤ h T) (hR : ∀ j ∈ R, j < T → cap j ≤ h j) :
    A * ((l : ℝ) ^ T)⁻¹ + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      ∑' e, h e := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hterm : ∀ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      if j < T then h j else 0 := by
    intro j hj
    split_ifs with hjT
    · have hpos : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹ := by positivity
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (max_le (by linarith) zero_le_one) (hcap j)
        _ = cap j := mul_one _
        _ ≤ h j := hR j hj hjT
    · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ hl1 (not_lt.mp hjT)
      rw [max_eq_right (by linarith), mul_zero]
  have hsumR : ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      ∑ j ∈ Finset.range T, h j := by
    calc _ ≤ ∑ j ∈ R, (if j < T then h j else 0) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ R.filter (· < T), h j := (Finset.sum_filter _ _).symm
      _ ≤ ∑ j ∈ Finset.range T, h j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter] at hj
          exact Finset.mem_range.mpr hj.2
        · intro i _ _
          exact hh i
  have hA : A * ((l : ℝ) ^ T)⁻¹ ≤ h T := by rw [← div_eq_mul_inv]; exact hT
  calc A * ((l : ℝ) ^ T)⁻¹ + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0
      ≤ ∑ j ∈ Finset.range T, h j + h T := by linarith
    _ = ∑ j ∈ Finset.range (T + 1), h j := (Finset.sum_range_succ _ _).symm
    _ ≤ ∑' e, h e := Summable.sum_le_tsum _ (fun i _ => hh i) hsum

theorem asmA_top_choice (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (D : ℕ∞)
    (hRodd : ∀ j ∈ R, Odd j)
    (hmin : ∀ e : ℕ, Odd e → (e : ℕ∞) < D → min (A / (l : ℝ) ^ e) (cap e) ≤ h e)
    (hD : ∀ e : ℕ, D = e → A / (l : ℝ) ^ e ≤ h e) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0 ≤ ∑' e, h e := by
  classical
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hcapj : ∀ j : ℕ, Odd j → (j : ℕ∞) < D → ¬ (A / (l : ℝ) ^ j ≤ h j) → cap j ≤ h j :=
    fun j hj hjD hn => (min_le_iff.mp (hmin j hj hjD)).resolve_left hn
  by_cases hS : ∃ e : ℕ, Odd e ∧ (e : ℕ∞) < D ∧ A / (l : ℝ) ^ e ≤ h e
  · have hTs := Nat.find_spec hS
    refine ⟨((l : ℝ) ^ Nat.find hS)⁻¹, by positivity, ?_, ?_⟩
    · intro e he
      have hlt : (Nat.find hS : ℕ∞) < (e : ℕ∞) := lt_of_lt_of_eq hTs.2.1 he
      have hle : Nat.find hS ≤ e := le_of_lt (ENat.coe_lt_coe.mp hlt)
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hl1 hle)
    · apply asmA_top_core l hl A cap h hcap hh hsum R (Nat.find hS) hTs.2.2
      intro j hj hjT
      have hjD : (j : ℕ∞) < D := lt_trans (ENat.coe_lt_coe.mpr hjT) hTs.2.1
      exact hcapj j (hRodd j hj) hjD
        (fun hle => Nat.find_min hS hjT ⟨hRodd j hj, hjD, hle⟩)
  · push_neg at hS
    have hcapR : ∀ j ∈ R, (j : ℕ∞) < D → cap j ≤ h j := fun j hj hjD =>
      hcapj j (hRodd j hj) hjD (not_le.mpr (hS j (hRodd j hj) hjD))
    by_cases hDt : D = ⊤
    · subst hDt
      refine ⟨0, le_rfl, fun e he => absurd he (ENat.top_ne_coe e), ?_⟩
      calc A * 0 + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * 0) 0 = ∑ j ∈ R, cap j := by simp
        _ ≤ ∑ j ∈ R, h j := Finset.sum_le_sum fun j hj => hcapR j hj (ENat.coe_lt_top j)
        _ ≤ ∑' e, h e := Summable.sum_le_tsum R (fun i _ => hh i) hsum
    · obtain ⟨e0, rfl⟩ := ENat.ne_top_iff_exists.mp hDt
      refine ⟨((l : ℝ) ^ e0)⁻¹, by positivity, fun e he => ?_, ?_⟩
      · have : e0 = e := by exact_mod_cast he
        rw [this]
      · exact asmA_top_core l hl A cap h hcap hh hsum R e0 (hD e0 rfl)
          (fun j hj hjT => hcapR j hj (ENat.coe_lt_coe.mpr hjT))

def asmA_f (l : ℕ) (A : ℝ) (cap : ℕ → ℝ) (D : ℕ∞) (e : ℕ) : ℝ :=
  if Odd e ∧ (e : ℕ∞) < D then max (A / (l : ℝ) ^ e - cap e) 0
  else if Odd e ∧ D < (e : ℕ∞) then A / (l : ℝ) ^ e else 0

def asmA_g (l : ℕ) (A : ℝ) (e : ℕ) : ℝ := if Odd e then A / (l : ℝ) ^ e else 0

theorem asmA_top_gen (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (hA : 0 ≤ A) (cap : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (D : ℕ∞) (hDodd : ∀ e : ℕ, D = e → Odd e) (R : Finset ℕ)
    (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      (∑' e, asmA_f l A cap D e) + (A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        A * gam l := by
  have hx : ∀ e : ℕ, 0 ≤ A / (l : ℝ) ^ e := fun e => div_nonneg hA (by positivity)
  have hf0 : ∀ e, 0 ≤ asmA_f l A cap D e := by
    intro e
    unfold asmA_f
    split_ifs
    · exact le_max_right _ _
    · exact hx e
    · exact le_rfl
  have hfg : ∀ e, asmA_f l A cap D e ≤ asmA_g l A e := by
    intro e
    unfold asmA_f asmA_g
    by_cases ho : Odd e
    · rw [if_pos ho]
      split_ifs
      · exact max_le (by linarith [hcap e]) (hx e)
      · exact le_rfl
      · exact hx e
    · rw [if_neg ho, if_neg (fun h' => ho h'.1), if_neg (fun h' => ho h'.1)]
  have hgs : HasSum (asmA_g l A) (A * gam l) := by
    have hfun : asmA_g l A = fun i => A * (if Odd i then ((l : ℝ) ^ i)⁻¹ else 0) := by
      funext e
      unfold asmA_g
      split_ifs
      · rw [div_eq_mul_inv]
      · rw [mul_zero]
    rw [hfun]
    exact (asmA_odd_hasSum l hl).mul_left A
  have hfs : Summable (asmA_f l A cap D) :=
    Summable.of_nonneg_of_le hf0 hfg hgs.summable
  have hhs : Summable (fun e => asmA_g l A e - asmA_f l A cap D e) := hgs.summable.sub hfs
  have hmin : ∀ e : ℕ, Odd e → (e : ℕ∞) < D →
      min (A / (l : ℝ) ^ e) (cap e) ≤ asmA_g l A e - asmA_f l A cap D e := by
    intro e ho he
    unfold asmA_f asmA_g
    rw [if_pos ho, if_pos ⟨ho, he⟩]
    rcases le_total (A / (l : ℝ) ^ e) (cap e) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by linarith)]
      linarith
    · rw [min_eq_right h1, max_eq_left (by linarith)]
      linarith
  have hDv : ∀ e : ℕ, D = e → A / (l : ℝ) ^ e ≤ asmA_g l A e - asmA_f l A cap D e := by
    intro e he
    have ho := hDodd e he
    unfold asmA_f asmA_g
    rw [if_pos ho, if_neg (fun h' => by rw [he] at h'; exact lt_irrefl _ h'.2),
      if_neg (fun h' => by rw [he] at h'; exact lt_irrefl _ h'.2)]
    linarith
  obtain ⟨ε, hε0, hεD, hε⟩ := asmA_top_choice l hl A cap (fun e => asmA_g l A e - asmA_f l A cap D e)
    hcap (fun e => by linarith [hfg e]) hhs R D hR hmin hDv
  refine ⟨ε, hε0, hεD, ?_⟩
  have htot : ∑' e, asmA_f l A cap D e + ∑' e, (asmA_g l A e - asmA_f l A cap D e) = A * gam l := by
    rw [← Summable.tsum_add hfs hhs]
    simp only [add_sub_cancel]
    exact hgs.tsum_eq
  linarith

theorem asmA_dTop_odd {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) : Odd e := by
  classical
  by_cases hne : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT
  · have h1 : dTop d TT s = ((sInf {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT} : ℕ) : ℕ∞) := by
      rw [ENat.coe_sInf (s := {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT}) hne]
      rfl
    rw [h1] at h
    have hm := Nat.sInf_mem (s := {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT}) hne
    have he : sInf {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT} = e := by exact_mod_cast h
    rw [he] at hm
    exact hm.1
  · push_neg at hne
    have htop : dTop d TT s = ⊤ := by
      unfold dTop
      refine iInf_eq_top.mpr fun e' => iInf_eq_top.mpr fun h' => ?_
      exact absurd h'.2 (hne e' h'.1)
    rw [htop] at h
    exact absurd h (ENat.top_ne_coe e)

theorem asmA_top (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) (R : Finset ℕ) (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, dTop d TT s = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      topTerm l d TT nu1 nu2 s + ((nu1 s : ℝ) * ε +
        ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        (nu1 s : ℝ) * gam l := by
  obtain ⟨ε, h0, h1, h2⟩ := asmA_top_gen l hl (nu1 s : ℝ) (Nat.cast_nonneg _)
    (fun e => (capL d TT nu1 nu2 (s + (e : ZMod d)) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (dTop d TT s) (fun e he => asmA_dTop_odd TT s e he) R hR
  exact ⟨ε, h0, h1, h2⟩

theorem capacity_le_reachCapacity (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
    (s : ZMod d) (j : ℤ) (hj : j < 0) (hodd : Odd j)
    (hsz : l ^ (-j).toNat ≤ size (s + (j : ZMod d))) :
    capL d TT nu1 nu2 (s + (j : ZMod d)) ≤ Wcap l d TT nu1 nu2 size s := by
  have hnn : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
  have hi : Odd (-j).toNat := by
    have ho : Odd (((-j).toNat : ℕ) : ℤ) := by rw [hnn]; exact hodd.neg
    exact (Int.odd_coe_nat _).mp ho
  have hsj : s - (((-j).toNat : ℕ) : ZMod d) = s + (j : ZMod d) := by
    rw [show (((-j).toNat : ℕ) : ZMod d) = ((((-j).toNat : ℕ) : ℤ) : ZMod d) from
      (Int.cast_natCast _).symm, hnn, Int.cast_neg, sub_neg_eq_add]
  unfold Wcap
  apply le_csSup
  · refine (Set.finite_range (fun t : ZMod d => capL d TT nu1 nu2 t)).bddAbove.mono ?_
    rintro _ ⟨i, _, rfl⟩
    exact ⟨_, rfl⟩
  · refine ⟨(-j).toNat, ⟨hi, ?_⟩, ?_⟩
    · show l ^ (-j).toNat ≤ size (s - (((-j).toNat : ℕ) : ZMod d))
      rw [hsj]
      exact hsz
    · simp only [hsj]

def asmA_cost (l : ℕ) {d : ℕ} (eps : ZMod d → ℝ) : Option (ZMod d × ℤ) → ℝ
  | none => 0
  | some (s, j) =>
      if 0 < j then max (1 - (l : ℝ) ^ j.toNat * eps s) 0 else ((l : ℝ) ^ (-j).toNat)⁻¹

theorem asmA_cost_nonneg (l : ℕ) {d : ℕ} (eps : ZMod d → ℝ) (p : Option (ZMod d × ℤ)) :
    0 ≤ asmA_cost l eps p := by
  rcases p with _ | ⟨s, j⟩
  · simp [asmA_cost]
  · simp only [asmA_cost]
    split_ifs
    · exact le_max_right _ _
    · positivity

theorem asmA_row {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (hsig : ∀ s, 0 ≤ sig s)
    (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (κ : ι → ℕ) (i : ι)
    (htop : isTop i = true → spec i = none) :
    (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i))) - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := by
  have hk : (0 : ℝ) ≤ κ i := Nat.cast_nonneg _
  by_cases ht : isTop i = true
  · rw [if_pos ht, htop ht]
    simp [rowRad, ht, asmA_cost]
  · rw [if_neg ht]
    have hrr : rowRad l sig eps lt isTop spec i ≤ sig (lt i) + asmA_cost l eps (spec i) := by
      unfold rowRad
      rw [if_neg ht]
      rcases hsp : spec i with _ | ⟨s, j⟩
      · simp [asmA_cost]
      · simp only [asmA_cost]
        split_ifs with hj
        · exact max_le (le_add_of_nonneg_right (le_max_right _ _))
            (by linarith [le_max_left (1 - (l : ℝ) ^ j.toNat * eps s) 0, hsig (lt i)])
        · exact max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (hsig _))
    nlinarith [mul_le_mul_of_nonneg_left hrr hk]

theorem rowRadiusAssembly : ThmAAssembly := by
  intro l d _ hl hd hde TT nu1 nu2 size hn21 hn1s sig hsig ι _ lt isTop spec κ htop htopsum hnonsum
    hspec hcap
  classical
  have hl2 : 2 ≤ l := by omega
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsig.1.1 s).1
  obtain ⟨R, hRdef⟩ : ∃ R : Finset ℕ, R = ((Finset.univ.image
      (fun i => (spec i).elim (0 : ℤ) Prod.snd)).filter (fun j => 0 < j)).image Int.toNat :=
    ⟨_, rfl⟩
  have hRodd : ∀ j ∈ R, Odd j := by
    intro j hj
    rw [hRdef] at hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨k, ⟨⟨i, rfl⟩, hk⟩, rfl⟩ := hj
    rcases hsp : spec i with _ | ⟨s, j'⟩
    · rw [hsp] at hk
      simp at hk
    · obtain ⟨_, hodd, _⟩ := hspec i s j' hsp
      rw [hsp] at hk
      simp only [Option.elim] at hk ⊢
      have h1 : ((j'.toNat : ℕ) : ℤ) = j' := Int.toNat_of_nonneg hk.le
      exact (Int.odd_coe_nat _).mp (by rw [h1]; exact hodd)
  have hex : ∀ s, ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, dTop d TT s = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      topTerm l d TT nu1 nu2 s + ((nu1 s : ℝ) * ε +
        ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        (nu1 s : ℝ) * gam l :=
    fun s => asmA_top l d hl2 TT nu1 nu2 s R hRodd
  choose eps heps0 hepsD hepsT using hex
  refine ⟨eps, heps0, fun s _ e he => hepsD s e he, ?_⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ι → ℝ, ∀ i, X i = if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i)) := ⟨_, fun _ => rfl⟩
  have hrow : ∀ i, X i - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := fun i => by
    rw [hXdef]
    exact asmA_row l sig eps hsig0 lt isTop spec κ i (fun h => (htop i h).2)
  have hX : ∑ i, X i = ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) +
      Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) := by
    rw [hsig.2, ← Finset.sum_fiberwise Finset.univ lt X]
    have hs : ∀ s : ZMod d, ∑ i ∈ Finset.univ.filter (fun i => lt i = s), X i =
        (if s ∈ TT then (nu1 s : ℝ) * (gam l - eps s) else 0) +
          (Dl d TT nu1 size s : ℝ) * (gam l - sig s) := by
      intro s
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun i => isTop i = true),
        Finset.filter_filter, Finset.filter_filter]
      rw [Finset.filter_congr (p := fun i => lt i = s ∧ ¬isTop i = true)
        (q := fun i => lt i = s ∧ isTop i = false) (fun i _ => by simp)]
      congr 1
      · have e1 : ∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), X i =
            (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) *
              (gam l - eps s) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_filter] at hi
          rw [hXdef, if_pos hi.2.2, hi.2.1]
        rw [e1]
        split_ifs with hsT
        · rw [htopsum s hsT]
        · have hem : Finset.univ.filter (fun i => lt i = s ∧ isTop i = true) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro h1 h2
            exact hsT (h1 ▸ (htop i h2).1)
          rw [hem]
          simp
      · have e2 : ∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), X i =
            (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) *
              (gam l - sig s) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_filter] at hi
          rw [hXdef, if_neg (by rw [hi.2.2]; exact Bool.false_ne_true), hi.2.1]
        rw [e2, hnonsum s]
    rw [Finset.sum_congr rfl (fun s _ => hs s), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter]
  obtain ⟨P, hPdef⟩ : ∃ P : Finset (ZMod d × ℤ), P = Finset.univ.biUnion (fun i => (spec i).toFinset) :=
    ⟨_, rfl⟩
  have hPmem : ∀ p ∈ P, ∃ i, spec i = some p := by
    intro p hp
    rw [hPdef, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hi⟩ := hp
    exact ⟨i, Option.mem_toFinset.mp hi⟩
  have hstepA : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) =
      ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) := by
    have hR : ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) = ∑ i, ∑ p ∈ P,
          (if spec i = some p then (κ i : ℝ) * asmA_cost l eps (some p) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_mul, Finset.sum_filter]
    rw [hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hsp : spec i with _ | p0
    · simp [asmA_cost]
    · have hp0 : p0 ∈ P := by
        rw [hPdef, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, Option.mem_toFinset.mpr hsp⟩
      rw [Finset.sum_eq_single p0]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro h
        exact hp (Option.some_injective _ h).symm
      · intro h
        exact absurd hp0 h
  have hstepB : ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) ≤
      ∑ p ∈ P, (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) :=
    Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_right (hcap p.1 p.2) (asmA_cost_nonneg l eps _)
  have hpos : ∑ p ∈ P.filter (fun p => 0 < p.2),
        (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) ≤
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 := by
    obtain ⟨G, hG⟩ : ∃ G : ZMod d × ℕ → ℝ, ∀ x, G x =
        (capL d TT nu1 nu2 (x.1 + (x.2 : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ x.2 * eps x.1) 0 :=
      ⟨_, fun _ => rfl⟩
    have hinj : Set.InjOn (fun p : ZMod d × ℤ => (p.1, p.2.toNat))
        (P.filter (fun p => 0 < p.2) : Set (ZMod d × ℤ)) := by
      rintro ⟨a, j⟩ hp ⟨b, j'⟩ hp' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).2
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega⟩
    calc ∑ p ∈ P.filter (fun p => 0 < p.2),
          (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p)
        = ∑ p ∈ P.filter (fun p => 0 < p.2), G (p.1, p.2.toNat) := by
          refine Finset.sum_congr rfl ?_
          rintro ⟨s, j⟩ hp
          have hj := (Finset.mem_filter.mp hp).2
          have hcast : ((j.toNat : ℕ) : ZMod d) = (j : ZMod d) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg hj.le]
          rw [hG]
          dsimp only at hj ⊢
          simp only [asmA_cost, if_pos hj, hcast]
      _ = ∑ x ∈ (P.filter (fun p => 0 < p.2)).image (fun p : ZMod d × ℤ => (p.1, p.2.toNat)), G x :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ TT ×ˢ R, G x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨⟨s, j⟩, hp, rfl⟩ := hx
            rw [Finset.mem_filter] at hp
            obtain ⟨i, hi⟩ := hPmem _ hp.1
            obtain ⟨hsT, -⟩ := hspec i s j hi
            rw [Finset.mem_product]
            refine ⟨hsT, ?_⟩
            rw [hRdef]
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, ⟨⟨i, by rw [hi]; rfl⟩, hp.2⟩, rfl⟩
          · intro x _ _
            rw [hG]
            exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
      _ = _ := by
          rw [Finset.sum_product]
          simp only [hG]
  have hneg : ∑ p ∈ P.filter (fun p => ¬ 0 < p.2),
        (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) ≤
      ∑ s ∈ TT, gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := by
    have hmaps : ∀ p ∈ P.filter (fun p => ¬ 0 < p.2), p.1 ∈ TT := by
      intro p hp
      obtain ⟨i, hi⟩ := hPmem p (Finset.mem_filter.mp hp).1
      exact (hspec i p.1 p.2 hi).1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun s _ => ?_
    obtain ⟨Q, hQ⟩ : ∃ Q : Finset (ZMod d × ℤ),
        Q = (P.filter (fun p => ¬ 0 < p.2)).filter (fun p => p.1 = s) := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : ∀ p ∈ Q, p.1 = s ∧ p.2 < 0 ∧ Odd p.2 ∧ ∃ i, spec i = some p := by
      intro p hp
      rw [hQ, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hpP, hn⟩, hps⟩ := hp
      obtain ⟨i, hi⟩ := hPmem p hpP
      have ho := (hspec i p.1 p.2 hi).2.1
      have hne : p.2 ≠ 0 := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact ⟨hps, by omega, ho, i, hi⟩
    have hinj2 : Set.InjOn (fun p : ZMod d × ℤ => (-p.2).toNat) (Q : Set (ZMod d × ℤ)) := by
      rintro ⟨a, j⟩ hp ⟨b, j'⟩ hp' h
      have h1 := hQmem _ (Finset.mem_coe.mp hp)
      have h2 := hQmem _ (Finset.mem_coe.mp hp')
      dsimp only at h h1 h2
      rw [Prod.mk.injEq]
      exact ⟨h1.1.trans h2.1.symm, by omega⟩
    have hoddN : ∀ n ∈ Q.image (fun p : ZMod d × ℤ => (-p.2).toNat), Odd n := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨⟨a, j⟩, hp, rfl⟩ := hn
      obtain ⟨-, hj, hodd, -⟩ := hQmem _ hp
      dsimp only at hj hodd ⊢
      have h1 : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      exact (Int.odd_coe_nat _).mp (by rw [h1]; exact hodd.neg)
    calc ∑ p ∈ Q, (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p)
        ≤ ∑ p ∈ Q, (Wcap l d TT nu1 nu2 size s : ℝ) * ((l : ℝ) ^ (-p.2).toNat)⁻¹ := by
          refine Finset.sum_le_sum ?_
          rintro ⟨s', j⟩ hp
          obtain ⟨hs', hj, hodd, i, hi⟩ := hQmem _ hp
          dsimp only at hs' hj hodd hi ⊢
          subst hs'
          obtain ⟨-, -, hlt, -, hsz⟩ := hspec i s' j hi
          have hsz' := hsz hj
          rw [hlt] at hsz'
          simp only [asmA_cost, if_neg (not_lt.mpr hj.le)]
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast capacity_le_reachCapacity l d TT nu1 nu2 size s' j hj hodd hsz') (by positivity)
      _ = (Wcap l d TT nu1 nu2 size s : ℝ) *
            ∑ n ∈ Q.image (fun p : ZMod d × ℤ => (-p.2).toNat), ((l : ℝ) ^ n)⁻¹ := by
          rw [Finset.mul_sum, Finset.sum_image hinj2]
      _ ≤ (Wcap l d TT nu1 nu2 size s : ℝ) * gam l :=
          mul_le_mul_of_nonneg_left (asmA_sum_odd_le l hl2 _ hoddN) (Nat.cast_nonneg _)
      _ = gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := mul_comm _ _
  have hcost : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 +
        ∑ s ∈ TT, gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := by
    rw [hstepA]
    refine le_trans hstepB ?_
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => 0 < p.2)]
    exact add_le_add hpos hneg
  have hsr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  rw [Finset.sum_sub_distrib] at hsr
  have hT : ∑ s ∈ TT, topTerm l d TT nu1 nu2 s ≤ ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) -
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [mul_sub]
    linarith [hepsT s]
  rw [Finset.sum_sub_distrib]
  linarith [hX, hcost, hT, hsr]

end Formalism.DworkPowerSeriesWeights
