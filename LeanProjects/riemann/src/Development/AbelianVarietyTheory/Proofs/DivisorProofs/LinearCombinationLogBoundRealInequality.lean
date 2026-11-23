import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunDen
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu

noncomputable section

open NumberField IsDedekindDomain Finset
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp n_vp c_vp a0 delta_vp IsClassZetaVals)

namespace GlobalTheory.DenSumPf

section Generic

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem c_vp_nonneg (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (l : ℕ) : 0 ≤ c_vp 𝔣 l := by
  unfold c_vp delta_vp; split_ifs <;> positivity

theorem toricBetaDenominatorBound_div_twelve_eq (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ) (l : ℕ) :
    betaBound_vp d s κ 𝔣 z l / 12 = ((cE_vp l z + Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ * a0 𝔣 l : ℕ) : ℝ) + n_vp d s κ 𝔣 l := by
  unfold betaBound_vp; push_cast; ring

theorem linear_combination_log_bound_real_inequality (K k2 c t lg Λ : ℝ) (hK : 0 ≤ K) (hk : 0 ≤ k2) (ht0 : 0 ≤ t) (ht : t ≤ 3 / 2) (hlg : 0 ≤ lg)
    (hc : c * lg ≤ Λ) (hlΛ : lg ≤ Λ) : (K * c + k2 * (2 * c + 1 + t)) * lg ≤ (K + 5 * k2) * Λ := by
  have hΛ : 0 ≤ Λ := hlg.trans hlΛ
  have h3 : t * lg ≤ 3 / 2 * Λ := mul_le_mul ht hlΛ hlg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hc hK, mul_le_mul_of_nonneg_left hc hk, mul_le_mul_of_nonneg_left hlΛ hk,
    mul_le_mul_of_nonneg_left h3 hk, mul_nonneg hk hΛ]

theorem n_vp_nonneg (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (l : ℕ) : 0 ≤ n_vp d s κ 𝔣 l := by
  have hc0 := c_vp_nonneg 𝔣 l
  unfold n_vp Formalism.PairingDivisionLocalBalance.nl
  split_ifs <;> positivity

theorem n_vp_log_le (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (l : ℕ) {Λ : ℝ} (hl : 0 ≤ Real.log l)
    (hcΛ : c_vp 𝔣 l * Real.log l ≤ Λ) (hlΛ : Real.log l ≤ Λ) :
    n_vp d s κ 𝔣 l * Real.log l ≤ (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ)) * Λ := by
  have hΛ : 0 ≤ Λ := hl.trans hlΛ
  unfold n_vp
  by_cases h : c_vp 𝔣 l = 0
  · rw [if_pos h, zero_mul]; positivity
  · rw [if_neg h]
    unfold Formalism.PairingDivisionLocalBalance.nl
    exact linear_combination_log_bound_real_inequality _ _ _ _ _ _ (by positivity) (by positivity) (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) hl hcΛ hlΛ

theorem ceil_log_le (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (GlobalTheory.CMVal.OF E)) (z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ) (l : ℕ)
    {Λ : ℝ} (hl : 0 ≤ Real.log l) (hcΛ : c_vp 𝔣 l * Real.log l ≤ Λ) (hlΛ : Real.log l ≤ Λ) (ha : a0 𝔣 l ≤ 2) :
    ((⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) : ℝ) * Real.log l ≤ (cE_vp l z : ℝ) * Real.log l +
      (((2 * s * Fintype.card I : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) + 2 * (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) + 1) * Λ := by
  have hΛ : 0 ≤ Λ := hl.trans hlΛ
  have hn0 := n_vp_nonneg d s κ 𝔣 l
  have hn := n_vp_log_le d s κ 𝔣 l hl hcΛ hlΛ
  rw [toricBetaDenominatorBound_div_twelve_eq, add_comm, Nat.ceil_add_natCast hn0]
  have h1 := Nat.ceil_lt_add_one hn0
  have ha' : (a0 𝔣 l : ℝ) ≤ 2 := by exact_mod_cast ha
  have hM : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ := by positivity
  push_cast at hn ⊢
  have h2 : ((⌈n_vp d s κ 𝔣 l⌉₊ : ℕ) : ℝ) * Real.log l ≤ (n_vp d s κ 𝔣 l + 1) * Real.log l :=
    mul_le_mul_of_nonneg_right h1.le hl
  have h3 : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) * a0 𝔣 l * Real.log l ≤ 2 * (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) * Λ := by
    have : (a0 𝔣 l : ℝ) * Real.log l ≤ 2 * Λ := by nlinarith [mul_le_mul_of_nonneg_right ha' hl]
    nlinarith [mul_le_mul_of_nonneg_left this hM]
  nlinarith

theorem delta_log_le (l : ℕ) (hl : l.Prime) :
    delta_vp E l * Real.log l ≤ Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by
  have hd : discr E ≠ 0 := discr_ne_zero E
  have hpos : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rw [Real.log_rpow hpos]
  have hdvd : l ^ padicValNat l (discr E).natAbs ∣ (discr E).natAbs := pow_padicValNat_dvd
  have hle : l ^ padicValNat l (discr E).natAbs ≤ (discr E).natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hd) hdvd
  have hle' : ((l : ℝ)) ^ padicValNat l (discr E).natAbs ≤ |(discr E : ℝ)| := by
    have e : (((discr E).natAbs : ℕ) : ℝ) = |(discr E : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← e]; exact_mod_cast hle
  have hlog : (padicValNat l (discr E).natAbs : ℝ) * Real.log l ≤ Real.log |(discr E : ℝ)| := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (by exact_mod_cast hl.pos) _) hle'
  unfold delta_vp
  rw [show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl, div_mul_eq_mul_div, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hlog hn.le

end Generic

end GlobalTheory.DenSumPf

namespace GlobalTheory.DenSumPf

section Host

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

variable {D : D7} {T : Type} {Lc : LevCh D T}

theorem maxConductorExponent_grid_le_two (P : Places Lc) (l : ℕ) : a0 (condF P) l ≤ 2 := by
  unfold a0
  apply csSup_le'
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.FunObj.SqNum.Model.expIn_condF]
  split_ifs
  · unfold condExp; split_ifs <;> omega
  · omega

theorem maxConductorExponent_grid_eq_zero_of_good_prime (P : Places Lc) {l : ℕ} (hl : l.Prime) (h1 : l ≠ D.host.g 0) (h2 : l ≠ D.host.g 1)
    (h3 : l ≠ D.host.pde) (h4 : l ≠ D.host.pde') (h5 : l ≠ q0 D) : a0 (condF P) l = 0 := by
  refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
  rintro _ ⟨v, hv, rfl⟩
  rw [GlobalTheory.FunObj.SqNum.Model.expIn_condF]
  split_ifs with hS
  · exfalso
    rcases P.mem_S0_of_sum_eq.1 hS with rfl | hS1
    · exact h5 (prime_unique hl (leastSplitAuxiliaryPrimeThetaChain_spec D).1 hv P.basePlace_over_qZero)
    · rcases (S1_mem_OmF D).1 hS1 with h | h | h | h
      · exact h1 (prime_unique hl (D.host.g_prime 0) hv h)
      · exact h2 (prime_unique hl (D.host.g_prime 1) hv h)
      · exact h3 (prime_unique hl D.host.pde_prime hv h)
      · exact h4 (prime_unique hl D.host.pde'_prime hv h)
  · exact le_rfl

end Host

end GlobalTheory.DenSumPf

namespace GlobalTheory.DenSumPf

theorem cE_sum_le (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) {E : Type} [Field E] [NumberField E] [IsCMField E] {s : ℕ}
    (hs : 1 ≤ s) (h16 : 16 ≤ Module.finrank ℚ (maximalRealSubfield E) * (2 * s))
    {z : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ} (hz : IsClassZetaVals (2 * s) z) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l ≤ ((Module.finrank ℚ (maximalRealSubfield E) * (2 * s) : ℕ) : ℝ) *
      Real.log (((Module.finrank ℚ (maximalRealSubfield E) * (2 * s) : ℕ) : ℝ) + 1) := by
  obtain ⟨hfin, hsum⟩ := ((hZ E s hs).2 z hz).2 h16
  set g : Nat.Primes → ℝ := fun l => (GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.cE z (l : ℕ) : ℝ) * Real.log (l : ℕ) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le))
  let Tp : Finset Nat.Primes := S.subtype Nat.Prime
  have e1 : ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l = ∑ p ∈ Tp, g p :=
    (Finset.sum_subtype_of_mem (fun l => (cE_vp l z : ℝ) * Real.log l) hS).symm
  rw [e1]
  refine le_trans ?_ hsum
  rw [finsum_eq_sum_of_support_subset g (s := Tp ∪ hfin.toFinset) (by
    intro x hx; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hx)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun p _ _ => hg0 p)

end GlobalTheory.DenSumPf

namespace GlobalTheory.DenSumPf

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

section Sizes

variable {D : D7}

theorem halfRank_le_bigN (i j : Fin D.R.m) : halfRank D i j ≤ bigN D := by
  have a : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
    have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
    simp only [rankV, bigN, Ranks.r, mul_add] at *
    omega
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  unfold halfRank; omega

theorem bigN_le (D : D7) : bigN D ≤ 8 * (D.R.N D.R.m) ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have e : bigN D = D.R.N D.R.m + D.R.m * D.R.k + D.R.m * D.R.m + 5 * D.R.m := by
    simp only [bigN, sLen, Ranks.r, Ranks.N]
    have : D.R.k + D.R.m - 1 + 6 = D.R.k + D.R.m + 5 := by omega
    rw [this]; ring
  have hkN : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
  have hmN : D.R.m ≤ D.R.N D.R.m := by
    unfold Ranks.N; have := Nat.le_mul_of_pos_right D.R.m (Nat.succ_pos D.R.t); omega
  have h1 : 1 ≤ D.R.N D.R.m := by omega
  rw [e]
  nlinarith [Nat.mul_le_mul hmN hkN, Nat.mul_le_mul hmN hmN, Nat.mul_le_mul h1 hmN]

theorem two_s_f_le (large₂ : SizeData₂ D) (hR : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) {s : ℕ}
    (hs : s ≤ halfRank D i j) : ((2 * s * D.R.f : ℕ) : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, hm44, -, hmfN, -⟩ := hR
  have h1 : s ≤ 8 * (D.R.N D.R.m) ^ 2 := hs.trans ((halfRank_le_bigN i j).trans (bigN_le D))
  have hd : 1 ≤ D.host.d := D.host.hyp.2.1.one_lt.le
  have h2 : 2 * s * D.R.f ≤ D.R.m * D.R.f * (D.R.N D.R.m) ^ 2 * D.host.d := by
    generalize (D.R.N D.R.m) ^ 2 = M at h1 ⊢
    calc 2 * s * D.R.f ≤ 16 * M * D.R.f := Nat.mul_le_mul_right _ (by omega)
      _ = 16 * (D.R.f * M) := by ring
      _ ≤ D.R.m * (D.R.f * M) := Nat.mul_le_mul_right _ (by omega)
      _ = D.R.m * D.R.f * M * 1 := by ring
      _ ≤ D.R.m * D.R.f * M * D.host.d := Nat.mul_le_mul_left _ hd
  calc ((2 * s * D.R.f : ℕ) : ℝ) ≤ ((D.R.m * D.R.f * (D.R.N D.R.m) ^ 2 * D.host.d : ℕ) : ℝ) := by exact_mod_cast h2
    _ ≤ large₂.sc.b := by push_cast; exact hmfN

theorem kap_le (large₂ : SizeData₂ D) (hR : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) (s : ℕ) (τ : D.what₂.Tau) :
    (kap D 1 i j s τ : ℝ) ≤ 5 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hhc, -⟩ := hR
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have he : ((num D 1 τ).e (j + 1) : ℝ) ≤ 4 * large₂.sc.b := by
    have e := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 j
    have h := (hhc τ j).2
    rw [e] at h
    exact_mod_cast h
  have hc : (cen D 1 τ (D.R.m - i) : ℝ) ≤ large₂.sc.b := by
    have hv2 := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, by omega⟩
    have hcl := (large₂.cloud_v τ ⟨0, by omega⟩).2
    have e1 : ((D.R.m - i - 1 : ℕ) : ℚ) = D.R.m - i - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have e2 : ((D.R.m - i : ℕ) : ℚ) = D.R.m - i := by rw [Nat.cast_sub (by omega)]
    have e : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid (D.R.m - i) =
        (D.hc τ).v ⟨0, by omega⟩ + 1 / 2 + ((i : ℚ) + 3 / 2) * (gap D 1 : ℚ) := by
      have hv2' : (((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).v 2 : ℤ) : ℚ) = (D.hc τ).v ⟨0, by omega⟩ :=
        hv2.symm
      have hm : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).m = D.R.m := rfl
      have hga : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).ga = gap D 1 := rfl
      simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a]
      rw [hv2', hm, hga, e1, e2]
      ring
    have hfl : ((cen D 1 τ (D.R.m - i) : ℤ) : ℚ) ≤ (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid (D.R.m - i) :=
      Int.floor_le _
    rw [e] at hfl
    have hfl' : ((cen D 1 τ (D.R.m - i) : ℚ) : ℝ) ≤ ((((D.hc τ).v ⟨0, by omega⟩ + 1 / 2 + ((i : ℚ) + 3 / 2) * (gap D 1 : ℚ) : ℚ)) : ℝ) := by
      exact_mod_cast hfl
    push_cast at hfl'
    have hg0 : (0 : ℝ) ≤ gap D 1 := by positivity
    have hi' : (i : ℝ) + 3 / 2 ≤ D.R.m + 1 := by
      have : (i : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
      linarith
    have := mul_le_mul_of_nonneg_right hi' hg0
    have hcast : ((cen D 1 τ (D.R.m - i) : ℚ) : ℝ) = (cen D 1 τ (D.R.m - i) : ℝ) := by push_cast; rfl
    linarith
  have hb : 0 ≤ large₂.sc.b := (Real.exp_pos _).le
  unfold kap
  have hs : (0 : ℝ) ≤ s := by positivity
  rcases le_or_gt 0 ((num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) - s) with h | h
  · have e : (((num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) - s).toNat : ℝ) =
        (((num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) - s : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [e]; push_cast; linarith
  · rw [Int.toNat_of_nonpos h.le]; push_cast; linarith

theorem absK_le (large₂ : SizeData₂ D) (hR : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) (s : ℕ) :
    (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) ≤ D.R.f * (5 * large₂.sc.b) := by
  unfold Formalism.PairingDivisionLocalBalance.absK
  push_cast
  calc ∑ τ, (kap D 1 i j s τ : ℝ) ≤ ∑ _τ : D.what₂.Tau, 5 * large₂.sc.b :=
        Finset.sum_le_sum fun τ _ => kap_le large₂ hR i j s τ
    _ = D.R.f * (5 * large₂.sc.b) := by rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

end Sizes

def badPr (D : D7) : Finset ℕ :=
  Finset.univ.image ![D.host.g 0, D.host.g 1, D.host.pde, D.host.pde', q0 D]

theorem card_badPr (D : D7) : (badPr D).card ≤ 5 :=
  (Finset.card_image_le).trans (by simp)

end GlobalTheory.DenSumPf

namespace GlobalTheory.DenSumPf

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

set_option maxHeartbeats 1000000 in

theorem denSum (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (_hF : FieldDat) : DenSum := by
  refine ⟨0, fun ε CF _ => ⟨8000, 1, fun C hC D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩
  intro i j s hs1 hs2 n hn S hS
  obtain ⟨z, hzv, hz⟩ := hn
  refine ⟨fun l hl => by rw [hz l (hS l hl)]; positivity, ?_⟩
  have hSR := hR.size
  obtain ⟨-, hSA, hm4, hm44, -, -, -, hg, hq0, hrd1, hrd2, -⟩ := hSR
  have hPde : Real.log (D.host.pde : ℝ) ≤ large₂.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ large₂.sc.L :=
    hSA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hL1 : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hx0 : 0 < Real.log large₂.sc.x := Real.log_pos large₂.sc.one_lt_alt
  have hf1 : 1 ≤ D.R.f := by have := D.R.n_pos'; unfold Ranks.f; omega
  have hf1' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1

  have hq := D.host.hyp.1
  have hd := D.host.hyp.2.1
  have hcpos : 0 < LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE; have := hq.pos; have := hd.pos; have := D.host.QS_pos; positivity
  have hlog : ∀ l ∈ badPr D, Real.log l ≤ 9 * large₂.sc.L + 1 := by
    intro l hl
    simp only [badPr, Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_succ, Fin.exists_fin_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | h
    · exact hg 0
    · exact hg 1
    · linarith [hPde.1]
    · linarith [hPde.2]
    · linarith [hq0]
    · exact h.elim
  set Λ : ℝ := 18 * large₂.sc.L + 2 with hΛ
  set κ := kap D 1 i j s with hκ
  set K : ℝ := ((2 * s * Fintype.card D.what₂.Tau : ℕ) : ℝ) + 5 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) +
    2 * (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) + 1 with hK
  have keyB : ∀ l ∈ S.filter (· ∈ badPr D), (n l) * Real.log l ≤ (cE_vp l z : ℝ) * Real.log l + K * Λ := by
    intro l hl
    obtain ⟨hl, hb⟩ := Finset.mem_filter.1 hl
    have hp := hS l hl
    have hl0 : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rw [hz l hp]
    have h9 := hlog l hb
    refine ceil_log_le _ _ _ _ _ _ hl0 ?_ (by linarith) (maxConductorExponent_grid_le_two G.pl l)
    unfold c_vp
    split_ifs
    · have : (a0 (condF G.pl) l : ℝ) ≤ 2 := by exact_mod_cast maxConductorExponent_grid_le_two G.pl l
      nlinarith
    · have h1 := delta_log_le (E := D.host.E) l hp
      have h2 : Real.log (|(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))) =
          Real.log D.host.rdE := rfl
      linarith
  have haO : ∀ l ∈ S.filter (fun l => ¬ l ∈ badPr D), a0 (condF G.pl) l = 0 := by
    intro l hl
    obtain ⟨hl, hb⟩ := Finset.mem_filter.1 hl
    have hne : ∀ i : Fin 5, l ≠ ![D.host.g 0, D.host.g 1, D.host.pde, D.host.pde', q0 D] i := fun i e =>
      hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, e.symm⟩)
    exact maxConductorExponent_grid_eq_zero_of_good_prime G.pl (hS l hl) (hne 0) (hne 1) (hne 2) (hne 3) (hne 4)
  have keyO := UpperTheory.Ram.Fun.sum_ceil_off_le D.host.d s κ (condF G.pl) z (S.filter fun l => ¬ l ∈ badPr D)
    (fun l hl => hS l (Finset.mem_filter.1 hl).1) haO (N := LevelStarExponents.condE D) hcpos.ne'
    (fun l hl h => D.host.der.discr_primes.1 l hl h) (A := large₂.sc.L / 100) (hrd1.trans hrd2) hrd2

  have hfF : Module.finrank ℚ (maximalRealSubfield D.host.E) = D.R.f := Formalism.MainNotions.J.finrank_F_eq D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hkf := two_s_f_le large₂ hR.size i j hs2
  have h16 : 16 ≤ Module.finrank ℚ (maximalRealSubfield D.host.E) * (2 * s) := by
    rw [hfF]
    have : 44 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm44 4
    nlinarith
  have hcE := cE_sum_le hZ hs1 h16 hzv S hS
  rw [hfF] at hcE
  have hfk : ((D.R.f * (2 * s) : ℕ) : ℝ) ≤ large₂.sc.b := by rw [show D.R.f * (2 * s) = 2 * s * D.R.f by ring]; exact hkf
  have hlg : Real.log (((D.R.f * (2 * s) : ℕ) : ℝ) + 1) ≤ large₂.sc.L + 1 := by
    calc _ ≤ Real.log (2 * large₂.sc.b) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + large₂.sc.L := by rw [Real.log_mul (by norm_num) (by linarith), hlogb]
      _ ≤ large₂.sc.L + 1 := by have := Real.log_two_lt_d9; linarith
  have hcE' : ∑ l ∈ S, (cE_vp l z : ℝ) * Real.log l ≤ large₂.sc.b * (large₂.sc.L + 1) :=
    hcE.trans (mul_le_mul hfk hlg (Real.log_nonneg (by
      have : (0 : ℝ) ≤ ((D.R.f * (2 * s) : ℕ) : ℝ) := by positivity
      linarith)) (by linarith))

  have hA := absK_le large₂ hR.size i j s
  have hK' : K ≤ 49 * D.R.f * large₂.sc.b := by
    have e : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) = ((2 * s * Fintype.card D.what₂.Tau : ℕ) : ℝ) + 2 * (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) := by
      unfold Formalism.PairingDivisionLocalBalance.wtM; push_cast; ring
    rw [hK, e, D.what₂.card_Tau]
    nlinarith
  have hK0 : 0 ≤ K := by positivity

  have hsum : ∑ l ∈ S, (n l) * Real.log l ≤ large₂.sc.b * (large₂.sc.L + 1) + 8 * (K * Λ) := by
    have hKΛ : 0 ≤ K * Λ := mul_nonneg hK0 (by linarith)
    have hB : ∑ l ∈ S.filter (· ∈ badPr D), (n l) * Real.log l ≤
        ∑ l ∈ S.filter (· ∈ badPr D), (cE_vp l z : ℝ) * Real.log l + 5 * (K * Λ) := by
      refine (Finset.sum_le_sum keyB).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hc : ((S.filter (· ∈ badPr D)).card : ℝ) ≤ 5 := by
        exact_mod_cast (Finset.card_le_card fun l hl => (Finset.mem_filter.1 hl).2).trans (card_badPr D)
      nlinarith
    have hO : ∑ l ∈ S.filter (fun l => ¬ l ∈ badPr D), (n l) * Real.log l ≤
        ∑ l ∈ S.filter (fun l => ¬ l ∈ badPr D), (cE_vp l z : ℝ) * Real.log l + K * Λ := by
      rw [Finset.sum_congr rfl fun l hl => by rw [hz l (hS l (Finset.mem_filter.1 hl).1)]]
      refine keyO.trans (add_le_add le_rfl (mul_le_mul ?_ (by linarith) (by linarith) hK0))
      have : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ := by positivity
      linarith
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ badPr D)] at hcE' ⊢
    linarith
  refine hsum.trans ?_
  unfold bTH
  rw [hlogb]
  have hΛ' : Λ ≤ 20 * large₂.sc.L := by linarith
  have h1 : K * Λ ≤ 49 * D.R.f * large₂.sc.b * (20 * large₂.sc.L) :=
    mul_le_mul hK' hΛ' (by linarith) (by positivity)
  have h2 : large₂.sc.b * (large₂.sc.L + 1) ≤ 2 * D.R.f * large₂.sc.b * large₂.sc.L := by
    have h6 : large₂.sc.L + 1 ≤ 2 * D.R.f * large₂.sc.L := by nlinarith
    have := mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ large₂.sc.b)
    linarith
  have h3 : (0 : ℝ) ≤ D.R.f * large₂.sc.b * Real.log large₂.sc.x := by positivity
  have h4 : (0 : ℝ) ≤ D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) := by positivity
  have h5 : 8000 * (D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) ≤ C * (D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) :=
    mul_le_mul_of_nonneg_right hC h4
  have h7 : 0 ≤ D.R.f * large₂.sc.b * large₂.sc.L := by positivity
  have e1 : C * D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) = C * (D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) := by ring
  have e2 : 49 * D.R.f * large₂.sc.b * (20 * large₂.sc.L) = 980 * (D.R.f * large₂.sc.b * large₂.sc.L) := by ring
  have e3 : 2 * D.R.f * large₂.sc.b * large₂.sc.L = 2 * (D.R.f * large₂.sc.b * large₂.sc.L) := by ring
  have e4 : D.R.f * large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) = D.R.f * large₂.sc.b * large₂.sc.L + D.R.f * large₂.sc.b * Real.log large₂.sc.x := by ring
  rw [e1]; rw [e2] at h1; rw [e3] at h2; rw [e4] at h5 ⊢
  linarith

end GlobalTheory.DenSumPf
