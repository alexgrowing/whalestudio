import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.PieriColumnMinors.SL2BinomialLattices
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightProdLeadingMinors
import Formalism.PieriBlockIdeals.PieriColumnMinors.WorkedExample

noncomputable section

open TensorProduct MvPolynomial

namespace Formalism.CohomologicalDescent.ShortWeightBounds

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds

theorem c_prime_le_short_bound_holds : CPrimeLeShort6 := by
  intro l k j t q h N' ecl xm xp mB I hl hI
  unfold cPrime cShort6 labelSumBoundPos
  have h1 := (harmonic_positive_log_holds l h I hI).1
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1
  have h4 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))
  linarith

theorem short_bound_le_coarse_holds : Short6LeCoarse := by
  intro l k j t q h N' ecl xm xp mB I
  have e : cCoarse l k j t q h N' ecl xm xp mB I =
      cShort6 l k j t q h N' ecl xm xp mB I + 6 * ((q : ℝ) + 2 * (j : ℝ)) := by
    unfold cCoarse cShort6
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : (0 : ℝ) ≤ 6 * ((q : ℝ) + 2 * (j : ℝ)) := by positivity
  linarith

theorem indexIntegral_nonneg_of_params (l : ℕ) (xm xp mB : ℤ) : 0 ≤ IlInd l xm xp mB := by
  unfold IlInd
  split_ifs <;> norm_num

theorem gated_min_nonneg_of_nonneg (l k t : ℕ) (D : ℤ) (I : ℝ) (hI : 0 ≤ I) :
    0 ≤ (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (I / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg hI (Nat.cast_nonneg _))
  · exact le_rfl

theorem short_bound_nonneg_holds : Short6Nonneg := by
  intro l k j t q h N' ecl xm xp mB I hl hx hI
  unfold cShort6
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h1 : 0 ≤ ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) hl1)
  have h2 : 0 ≤ (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (div_nonneg (by exact_mod_cast sub_nonneg.mpr hx) (Nat.cast_nonneg _))
      (indexIntegral_nonneg_of_params l xm xp mB))
  have h3 := gated_min_nonneg_of_nonneg l k t (xm - mB) I hI
  have h4 : 0 ≤ (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))) := by
    have := Real.posLog_nonneg (x := (h : ℝ) / (l : ℝ))
    exact mul_nonneg (div_nonneg hI (Nat.cast_nonneg _)) (by linarith)
  have h5 : (0 : ℝ) ≤ ecl := Nat.cast_nonneg _
  linarith

theorem theorem_w_top_short_bound_holds : TheoremWTopShort6 := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  have hl : l.Prime := hT.1
  have key : TopIncl O Γ jK l N lam S
      (∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ) := by
    refine top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_
      (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1
    apply Finset.sum_le_sum
    intro τ _
    unfold cTau
    split_ifs
    · exact min_le_min le_rfl (Nat.floor_le_floor
        (c_prime_le_short_bound_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))
    · exact le_rfl
  exact ⟨key, Nat.sInf_le key⟩

theorem kappa_floor_holds : KapFloor := by
  intro P l hl
  unfold Par.kap h0
  have hc : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hl, Nat.cast_one]
  rw [hc]
  exact Nat.floor_div_natCast P.h (l - 1)

theorem depth_nat_le_holds : DepthNatLe := by
  intro P ι W l τ hh hl
  unfold Wts.iW
  apply Nat.le_floor
  rw [← kappa_floor_holds P l hl]
  have h1 : ((h0 P : ℕ) : ℝ) ≤ P.h := Nat.floor_le hh
  show _ ≤ (W.q τ : ℝ) * P.h
    + ((l : ℝ) * (W.mwF P τ l : ℝ) + (W.mw P τ l : ℝ)) * ((P.t : ℝ) + 2 * (P.kap l : ℝ))
  push_cast
  have h2 : (W.q τ : ℝ) * (h0 P : ℝ) ≤ (W.q τ : ℝ) * P.h :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  linarith

theorem weight_on_block_eq_bot_add (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a : ℕ)
    (h1 : kc P + W.j τ ≤ a) (h2 : a < kc P + W.j τ + P.t) :
    W.U P τ a = W.bot P τ + ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℤ) := by
  have ht := hP.t_ge
  have e1 := hW.block τ a h1 h2
  have e2 := hW.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  unfold Wts.bot Wts.U UN
  rw [e1, e2]
  omega

theorem weights_strictAnti (P : Par) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a b : ℕ)
    (h1 : a < b) (h2 : b < P.Nr) : W.U P τ b < W.U P τ a := by
  have e1 := hW.anti τ a b h1.le h2
  unfold Wts.U UN
  omega

theorem weights_antitone_le (P : Par) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a b : ℕ)
    (h1 : a ≤ b) (h2 : b < P.Nr) : W.U P τ b ≤ W.U P τ a := by
  rcases h1.lt_or_eq with h | h
  · exact (weights_strictAnti P W hW τ a b h h2).le
  · rw [h]

theorem top_eq_bot_add_t_sub_one (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    W.top P τ = W.bot P τ + (P.t : ℤ) - 1 := by
  have ht := hP.t_ge
  have e := weight_on_block_eq_bot_add P hP W hW τ (kc P + W.j τ) le_rfl (by omega)
  unfold Wts.top
  rw [e]
  omega

theorem j_add_q_eq_m (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    W.j τ + W.q τ = P.m := by
  have h1 := hW.what₂ τ
  have h2 := hP.Nr_eq
  have h3 := hP.m_le
  have h4 := hP.m_pos
  unfold kc at h1
  omega

theorem abs_weight_sub_near_translation_le (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a : ℕ)
    (h1 : kc P ≤ a) (h2 : a < P.Nr) : |(W.U P τ a : ℝ) - W.c τ + W.e τ| ≤ P.η := by
  by_cases hb : kc P + W.j τ ≤ a ∧ a < kc P + W.j τ + P.t
  · have e := weight_on_block_eq_bot_add P hP W hW τ a hb.1 hb.2
    have hc := hW.centre τ
    have ht := hP.t_le
    have hd0 : (0 : ℝ) ≤ ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd1 : ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) ≤ (P.t : ℝ) - 1 := by
      have : kc P + W.j τ + P.t - 1 - a + 1 ≤ P.t := by omega
      have h3 : ((kc P + W.j τ + P.t - 1 - a + 1 : ℕ) : ℝ) ≤ (P.t : ℝ) := by exact_mod_cast this
      push_cast at h3
      linarith
    have e' : (W.U P τ a : ℝ) = (W.bot P τ : ℝ) + ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) := by
      rw [e]; push_cast; ring
    rw [e', abs_le]
    constructor <;> linarith
  · refine (hW.low τ a h2 ?_).2
    by_cases h3 : a < kc P + W.j τ
    · exact Or.inl ⟨h1, h3⟩
    · right
      by_contra h4
      exact hb ⟨by omega, by omega⟩

theorem rest_near_holds : RestNear := by
  intro P hP ι W hW τ
  exact ⟨fun a h1 h2 => abs_weight_sub_near_translation_le P hP W hW τ a h1 h2, fun a h1 h2 => weight_on_block_eq_bot_add P hP W hW τ a h1 h2,
    top_eq_bot_add_t_sub_one P hP W hW τ, j_add_q_eq_m P hP W hW τ, fun a b h1 h2 => weights_strictAnti P W hW τ a b h1 h2⟩

theorem two_eta_lt_b (P : Par) (hP : P.Hyp) (hL : P.Large) : 2 * P.η < P.b := by
  have h1 := two_mul_lstar_le_b hP hL
  have h2 := b_div_lstar_pos hP hL
  have h3 := hP.sum_lt
  have h4 := hP.b'_pos
  have h5 := hP.S_nonneg
  linarith

theorem weight_nonneg' (P : Par) {ι : Type} (W : Wts ι) (τ : ι) (a : ℕ) (h : a < P.Nr) :
    0 ≤ W.U P τ a := by
  unfold Wts.U UN
  omega

theorem weight_lt_lower_translation_of_thick (P : Par) (hP : P.Hyp) (hL : P.Large) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι)
    (hτ : τ ∈ W.T2) (a : ℕ) (h1 : kc P ≤ a) (h2 : a < P.Nr) : W.U P τ a < W.xm τ := by
  have h3 := abs_weight_sub_near_translation_le P hP W hW τ a h1 h2
  have h4 := (hW.thick τ hτ).1.1
  have h5 := two_eta_lt_b P hP hL
  have h6 := (hW.window τ).1
  have h7 := eta_nonneg' hP
  have h8 := (abs_le.mp h3).2
  have : (W.U P τ a : ℝ) < (W.xm τ : ℝ) := by linarith
  exact_mod_cast this

theorem rank_fits_block_and_t_ge_six (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    kc P + W.j τ + P.t ≤ P.Nr ∧ 6 ≤ P.t := by
  have h1 := hW.what₂ τ
  have h2 := hP.t_ge
  have h3 := hP.m_pos
  have h4 := hP.m_le
  omega

theorem shape_t_real_holds : ShapeTReal := by
  intro P hP hL ι W hW J τ hτ
  have hτ' : τ ∈ W.T2 := hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact weight_nonneg' P W τ _ (by omega)
  · exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ' _ (by omega) (by omega)
  · exact (hW.window τ).2.1
  · exact (hW.thick τ hτ').2
  · have h1 := (hW.window τ).1
    have h2 := (hW.window τ).2.2
    show ((W.xp τ - W.xm τ : ℤ) : ℝ) ≤ P.S
    push_cast
    linarith
  · have := j_add_q_eq_m P hP W hW τ
    show W.q τ + W.j τ ≤ P.m
    omega

theorem widths_real_holds : WidthsReal := by
  intro P ι W hW J τ hτ
  rcases hW.other τ hτ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem upper_translation_le_floor_height (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι)
    (hτ : τ ∈ W.T2) : W.xp τ ≤ (h0 P : ℤ) :=
  le_floor_h hP (hW.thick τ hτ).2

theorem weight_le_upper_translation_of_thick (P : Par) (hP : P.Hyp) (hL : P.Large) {ι : Type} (W : Wts ι) (hW : W.Ok P)
    (τ : ι) (hτ : τ ∈ W.T2) (a : ℕ) (h2 : a < P.Nr) : W.U P τ a ≤ W.xp τ := by
  by_cases h : a < kc P
  · exact (hW.cloud τ a h).2
  · have h1 := weight_lt_lower_translation_of_thick P hP hL W hW τ hτ a (by omega) h2
    have h3 := (hW.window τ).2.1
    omega

theorem shape_w_real_holds : ShapeWReal := by
  intro P hP hL ι W hW τ hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  have hx := upper_translation_le_floor_height P hP W hW τ hτ
  refine ⟨hW.what₂ τ, hW.anti τ, hW.block τ, ?_, hW.cloud τ, ?_, ?_, (hW.window τ).2.1, ?_⟩
  · have h1 := weight_le_upper_translation_of_thick P hP hL W hW τ hτ 0 (by omega)
    unfold Wts.U UN at h1
    omega
  · intro a h1 h2
    exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ a h1 (by omega)
  · exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ _ (by omega) (by omega)
  · have h1 := weight_nonneg' P W τ (kc P + W.j τ) (by omega)
    unfold Wts.U at h1
    omega

theorem toNat_cast_real_of_nonneg (z : ℤ) (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

theorem shape_a_real_holds : ShapeAReal := by
  intro P hP hL ι W hW τ hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  have hx := upper_translation_le_floor_height P hP W hW τ hτ
  have hw := hW.window τ
  have hS : 0 ≤ W.xp τ - W.xm τ := by have := hw.2.1; omega
  have hE : 0 ≤ W.U P τ (kc P) - W.U P τ (P.Nr - 1) := by
    have := weights_antitone_le P W hW τ (kc P) (P.Nr - 1) (by omega) (by omega)
    omega
  refine ⟨⟨?_, ?_, by omega, ?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    exact weights_strictAnti P W hW τ a b hab b.isLt
  · intro a
    refine ⟨weight_nonneg' P W τ a a.isLt, ?_⟩
    have := weight_le_upper_translation_of_thick P hP hL W hW τ hτ a a.isLt
    omega
  · intro a ha
    have h1 := hW.cloud τ a ha
    rw [Int.toNat_of_nonneg hS]
    exact ⟨h1.1, by omega⟩
  · intro a ha
    rw [Int.toNat_of_nonneg hE]
    have h1 := weights_antitone_le P W hW τ a (P.Nr - 1) (by have := a.isLt; omega) (by omega)
    have h2 := weights_antitone_le P W hW τ (kc P) a ha a.isLt
    exact ⟨h1, by omega⟩
  · rw [toNat_cast_real_of_nonneg _ hS]
    push_cast
    linarith [hw.1, hw.2.2]
  · rw [toNat_cast_real_of_nonneg _ hE]
    have h1 := abs_le.mp (abs_weight_sub_near_translation_le P hP W hW τ (kc P) le_rfl (by omega))
    have h2 := abs_le.mp (abs_weight_sub_near_translation_le P hP W hW τ (P.Nr - 1) (by omega) (by omega))
    push_cast
    linarith [h1.2, h2.1]

theorem weights_have_positive_shape (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    P.Shape (W.Uset P τ) (W.bot P τ) (W.c τ) (W.e τ) 1 := by
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · have := hW.centre τ
    push_cast
    linarith
  · intro u hu hnot
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    have ha' : a < P.Nr := Finset.mem_range.mp ha
    push_cast
    rw [one_mul]
    by_cases h1 : a < kc P
    · left
      have h2 := hW.cloud τ a h1
      have h3 := hW.window τ
      have h4 : (W.xm τ : ℝ) ≤ (W.U P τ a : ℝ) := by exact_mod_cast h2.1
      have h5 : (W.U P τ a : ℝ) ≤ (W.xp τ : ℝ) := by exact_mod_cast h2.2
      constructor <;> linarith [h3.1, h3.2.2]
    · right
      by_cases hb : kc P + W.j τ ≤ a ∧ a < kc P + W.j τ + P.t
      · exfalso
        apply hnot
        have e := weight_on_block_eq_bot_add P hP W hW τ a hb.1 hb.2
        rw [Finset.mem_Icc, e]
        constructor <;> omega
      · refine hW.low τ a ha' ?_
        by_cases h3 : a < kc P + W.j τ
        · exact Or.inl ⟨by omega, h3⟩
        · right
          by_contra h4
          exact hb ⟨by omega, by omega⟩

theorem shape_reflect (P : Par) (U : Finset ℤ) (bot H : ℤ) (c e : ℝ) (h : P.Shape U bot c e 1) :
    P.Shape (U.image (fun u => H - u)) (H - (bot + (P.t : ℤ) - 1)) ((H : ℝ) - c) e (-1) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · push_cast at h2 ⊢
    linarith
  · intro u' hu' hnot
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    have hn : u ∉ Finset.Icc bot (bot + (P.t : ℤ) - 1) := by
      intro hm
      apply hnot
      rw [Finset.mem_Icc] at hm ⊢
      constructor <;> omega
    have h4 := h3 u hu hn
    have e1 : (((-1 : ℤ) : ℝ)) * (((H - u : ℤ) : ℝ) - ((H : ℝ) - c)) = ((1 : ℤ) : ℝ) * ((u : ℝ) - c) := by
      push_cast; ring
    rw [e1]
    exact h4

theorem thick_or_top_or_thin (P : Par) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    P.Thick (W.e τ) ∨ P.Top (W.e τ) ∨ P.Thin (W.e τ) := by
  by_cases h : τ ∈ W.T2
  · exact Or.inl (hW.thick τ h).1
  · rcases hW.other τ h with h1 | h1
    · exact Or.inr (Or.inl h1.1)
    · exact Or.inr (Or.inr h1.1)

def placesOfParameters (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (J : ℕ → ℕ) :
    Places (W.sizeData₂ P J) P where
  U := W.Uset P
  bot := W.bot P
  c := W.c
  e := W.e
  σ := fun _ => 1
  UF := W.UsetF P
  botF := W.botF P
  cF := fun τ l => if W.cj l τ then ((h0 P : ℤ) : ℝ) - W.c (W.fr l τ) else W.c (W.fr l τ)
  eF := fun τ l => W.e (W.fr l τ)
  σF := fun τ l => if W.cj l τ then -1 else 1
  shape := fun τ => weights_have_positive_shape P hP W hW τ
  kind := fun τ => thick_or_top_or_thin P W hW τ
  shapeF := by
    intro τ l
    cases h : W.cj l τ
    · simp only [Wts.UsetF, Wts.botF, h, Bool.false_eq_true, if_false]
      exact weights_have_positive_shape P hP W hW _
    · simp only [Wts.UsetF, Wts.botF, h, if_true]
      rw [top_eq_bot_add_t_sub_one P hP W hW]
      exact shape_reflect P _ _ _ _ _ (weights_have_positive_shape P hP W hW _)
  kindF := fun τ l => thick_or_top_or_thin P W hW _
  mw_eq := fun _ _ => rfl
  mwF_eq := fun _ _ => rfl

theorem places_real_holds : PlacesReal := by
  intro P hP hL ι W hW J
  have hPl := placesOfParameters P hP W hW J
  exact ⟨⟨hPl⟩, noWindowOf_holds P hP hL ι (W.sizeData₂ P J) hPl⟩

theorem one_le_h (P : Par) (hH : P.Hyp) : 1 ≤ P.h := by
  have h1 : 0 < P.b := Real.exp_pos _
  have h2 := hH.S_nonneg
  have h3 := hH.t_le
  have h4 : (0 : ℝ) ≤ (P.t : ℝ) := Nat.cast_nonneg _
  unfold Par.h
  linarith

theorem floor_height_le_height (P : Par) (hH : P.Hyp) : (h0 P : ℝ) ≤ P.h := by
  unfold h0
  exact Nat.floor_le (by linarith [one_le_h P hH])

theorem one_le_floor_height (P : Par) (hH : P.Hyp) : 1 ≤ h0 P := by
  unfold h0
  exact Nat.le_floor (by exact_mod_cast one_le_h P hH)

theorem restriction_lambda_antitone {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) :
    Antitone (res P.Nr (W.lam τ)) := fun a b hab => hW.anti τ a b hab b.2

theorem kc_le_rank {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) : kc P ≤ P.Nr := by
  have := hW.what₂ τ
  omega

theorem restriction_lambda_antitone_kc {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) :
    Antitone (res (kc P) (W.lam τ)) :=
  fun a b hab => hW.anti τ a b hab (lt_of_lt_of_le b.2 (kc_le_rank hW τ))

theorem top_inputs_of_shape_w (hSW : ShapeWReal) : TopInputsReal := by
  intro P hH hL ι _ _ W hW l X hl hu hlJ ϖ n₀ e Λ L _ _ _ _ _ hwt hfin hϖ hA hT hS hI
  have hd := paramsLargePrime_holds P hH hL l hlJ
  have hsq : h0 P < l ^ 2 := by
    have h1 := hd.2.2.2.2.2.2.2
    have h2 := floor_height_le_height P hH
    have h3 : (0 : ℝ) ≤ (P.Nr : ℝ) := Nat.cast_nonneg _
    have h4 : (h0 P : ℝ) < (l : ℝ) ^ 2 := by linarith
    exact_mod_cast h4
  have ht : 1 ≤ P.t := by have := hH.t_ge; omega
  refine ⟨hl, RealLocalDeltaNabla.units_of_local_holds X.O l hl hu, hfin, hϖ, hsq, ht,
    fun τ hτ => hSW P hH hL ι W hW τ hτ, ?_, ?_, hA.1, hA.2, hT.1, hT.2, hS.1, hS.2, hI⟩
  · intro τ _ μ
    exact (exact_exponents_fit_holds l P.Nr (kc P) (W.lam τ) hl (restriction_lambda_antitone hW τ) (restriction_lambda_antitone_kc hW τ)).2 μ
  · intro τ
    exact (exact_exponents_fit_holds l P.Nr (kc P) (W.lam τ) hl (restriction_lambda_antitone hW τ) (restriction_lambda_antitone_kc hW τ)).1

theorem inclusion_w_of_shape_w (hSW : ShapeWReal) : InclWReal := by
  intro hD P hH hL ι _ _ W hW l X hl hu hlJ hWI
  obtain ⟨ϖ, n₀, e, Λ, L, _, _, _, _, _, hwt, hfin, hϖ, hA, hT, hS, hI⟩ := hWI
  have hTop := top_inputs_of_shape_w hSW P hH hL ι W hW l X hl hu hlJ ϖ n₀ e Λ L hwt hfin hϖ hA hT hS hI
  have h := theorem_w_top_short_bound_holds (last_graded_of_graded_alone hD) X.O X.A X.G X.Γ X.K X.jK ι l
    P.Nr (kc P) P.t (h0 P) W.lam W.T2 W.j W.q W.xm W.xp (fun τ => W.ecl P τ l)
    (fun τ => W.ex P τ l) (W.iW P l) X.T X.S ϖ n₀ e Λ L hwt hTop
  exact h

theorem exponent_mul_log_le_choose_mul_log (N l w e : ℕ) (y : ℝ) (he : e ≤ N.choose 2 * Nat.log l w) (hy : (w : ℝ) ≤ y)
    (hy1 : 1 ≤ y) : (e : ℝ) * Real.log l ≤ (N.choose 2 : ℝ) * Real.log y := by
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  rcases Nat.lt_or_ge l 2 with hl | hl
  · have h0l : Real.log (l : ℝ) = 0 := by
      interval_cases l <;> simp
    rw [h0l, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hlogy
  · have key : ((Nat.log l w : ℕ) : ℝ) * Real.log l ≤ Real.log y := by
      rcases Nat.eq_zero_or_pos w with hw | hw
      · simp [hw, hlogy]
      · have hpow : l ^ Nat.log l w ≤ w := Nat.pow_log_le_self l hw.ne'
        have h1 : ((l ^ Nat.log l w : ℕ) : ℝ) ≤ y := le_trans (by exact_mod_cast hpow) hy
        have hpos : (0 : ℝ) < ((l ^ Nat.log l w : ℕ) : ℝ) := by
          have : 0 < l ^ Nat.log l w := pow_pos (by omega) _
          exact_mod_cast this
        calc ((Nat.log l w : ℕ) : ℝ) * Real.log l
            = Real.log (((l ^ Nat.log l w : ℕ) : ℝ)) := by rw [Nat.cast_pow, Real.log_pow]
          _ ≤ Real.log y := Real.log_le_log hpos h1
    have hlogl : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ l))
    calc (e : ℝ) * Real.log l ≤ ((N.choose 2 * Nat.log l w : ℕ) : ℝ) * Real.log l :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast he) hlogl
      _ = (N.choose 2 : ℝ) * (((Nat.log l w : ℕ) : ℝ) * Real.log l) := by push_cast; ring
      _ ≤ (N.choose 2 : ℝ) * Real.log y := mul_le_mul_of_nonneg_left key (by positivity)

theorem weight_in_width_range {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) (a : ℕ) (ha : a < P.Nr) :
    W.U P τ (P.Nr - 1) ≤ UN P.Nr (W.lam τ) a ∧
      UN P.Nr (W.lam τ) a ≤ W.U P τ (P.Nr - 1) + ((W.width P τ).toNat : ℤ) := by
  have h1 := hW.anti τ a (P.Nr - 1) (by omega) (by omega)
  have h2 := hW.anti τ 0 a (by omega) ha
  have h3 := hW.anti τ 0 (P.Nr - 1) (by omega) (by omega)
  unfold Wts.width Wts.U UN
  omega

theorem width_nonneg {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (hN : 0 < P.Nr) (τ : ι) :
    0 ≤ W.width P τ := by
  have h3 := hW.anti τ 0 (P.Nr - 1) (by omega) (by omega)
  unfold Wts.width Wts.U UN
  omega

theorem rank_pos_of_hyp (P : Par) (hH : P.Hyp) : 0 < P.Nr := by
  have h1 := hH.Nr_eq
  have h2 := hH.t_ge
  omega

theorem one_le_k_of_hyp (P : Par) (hH : P.Hyp) : 1 ≤ P.k := le_trans hH.m_pos hH.m_le

theorem kc_cast_le_k (P : Par) : (kc P : ℝ) ≤ (P.k : ℝ) := by
  unfold kc
  exact_mod_cast Nat.sub_le _ _

theorem sizeData_depth_nonneg {ι : Type} (W : Wts ι) (P : Par) (hH : P.Hyp) (J : ℕ → ℕ) (τ : ι) (l : ℕ) :
    0 ≤ (W.sizeData₂ P J).depth P τ l := by
  have hh := one_le_h P hH
  unfold SizeData₂.depth
  have h1 : 0 ≤ ((W.sizeData₂ P J).q τ : ℝ) * P.h := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have h2 : 0 ≤ ((l : ℝ) * ((W.sizeData₂ P J).mwF τ l : ℝ) + ((W.sizeData₂ P J).mw τ l : ℝ)) *
      ((P.t : ℝ) + 2 * (P.kap l : ℝ)) := by positivity
  linarith

theorem correction_weight_eq_formula {ι : Type} (W : Wts ι) (P : Par) (J : ℕ → ℕ) (τ : ι) (l : ℕ) :
    (W.sizeData₂ P J).cW P τ l =
      ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
        + (W.ecl P τ l : ℝ)
        + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ))
        + (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
            min (min (P.k : ℝ) (P.t : ℝ))
              ((W.sizeData₂ P J).depth P τ l / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0)
        + ((W.sizeData₂ P J).depth P τ l / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := rfl

theorem top_inputs_real_holds : TopInputsReal := top_inputs_of_shape_w shape_w_real_holds

theorem inclusion_w_real_holds : InclWReal := inclusion_w_of_shape_w shape_w_real_holds

theorem linkage_depth_eq_sum_difference (N k j t q : ℕ) (hN : k + j + t + q = N) (lam : ℕ → ℕ) (w : Fin N → ℕ)
    (U U' : Fin (k + j + t + q) → ℤ) (hU : ∀ a, U a = UN N lam a)
    (hU' : ∀ (a : Fin (k + j + t + q)) (a' : Fin N), (a : ℕ) = (a' : ℕ) →
      U' a = (w a' : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)) :
    depth2 (res N (varpi (k + j))) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) := by
  subst hN
  rw [depth_as_weight_sum_holds]
  apply Finset.sum_congr rfl
  intro a _
  rw [hU, hU' a a rfl]

theorem image_univ_eq_image_range (N N' : ℕ) (hN : N' = N) (f : ℕ → ℤ) (U : Fin N' → ℤ) (hU : ∀ a, U a = f a) :
    Finset.univ.image U = (Finset.range N).image f := by
  subst hN
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, hU]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem depth_of_linkage_holds : DepthOfLink := by
  intro P hH hL ι W hW l hl hlJ τ w hlink
  obtain ⟨E, _, σ, _, O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, D, cst, ep, J, botJ, kap, ζ, em, jj, inc,
    hRefl, hLinked, hCar, hNI, hU, hbot, hσ, hU', hsum⟩ := hlink
  have hd := paramsLargePrime_holds P hH hL l hlJ
  have hl2 : l ≠ 2 := by
    have h1 := hd.2.2.2.2.2.1
    have h2 := rank_pos_of_hyp P hH
    omega
  have hkap := kappa_floor_holds P l hl.one_le
  have ht : P.t + 2 * (h0 P / (l - 1)) < l := by
    rw [← hkap]
    exact hd.2.2.2.1
  have hrows := hW.what₂ τ
  have hshape : WorkedExample.ShapeAt (kc P) (W.j τ) P.t (W.q τ) D (inc τ) := by
    refine ⟨fun a => ?_, hsum, fun a h1 h2 => ?_⟩
    · rw [hU]
      exact weight_nonneg' P W τ a (by have := a.2; omega)
    · rw [hU, hbot]
      exact weight_on_block_eq_bot_add P hH W hW τ a h1 h2
  have hDB := WorkedExample.orientation_lattice_holds E σ (kc P) (W.j τ) P.t (W.q τ) l (h0 P) O' F L' I Wl u c D cst ep
    J botJ kap (inc τ) ζ em jj hl2 ht hRefl hLinked hCar hNI hshape
  unfold WorkedExample.DepthBound at hDB
  have hmw : ∀ τ', D.mw l P.t (h0 P / (l - 1)) (inc τ') = W.mw P τ' l := by
    intro τ'
    unfold WorkedExample.Labels.mw Wts.mw Wts.Uset
    rw [hbot, hkap, image_univ_eq_image_range P.Nr _ hrows (W.U P τ') (D.U (inc τ')) (hU τ')]
  have hmwF : D.mw l P.t (h0 P / (l - 1)) (σ (inc τ)) = W.mwF P τ l := by
    rw [hσ]
    unfold Wts.mwF Wts.botF Wts.UsetF
    by_cases hc : W.cj l τ = true
    · rw [if_pos hc, if_pos hc, if_pos hc, WorkedExample.weight_letters_holds E _ D σ (h0 P) P.t hRefl, hmw]
      have e : (h0 P : ℤ) - W.top P (W.fr l τ) = (h0 P : ℤ) - (W.bot P (W.fr l τ) + (P.t : ℤ) - 1) := by
        rw [top_eq_bot_add_t_sub_one P hH W hW]
      rw [e, WorkedExample.weight_reflection_holds]
      rfl
    · rw [if_neg hc, if_neg hc, if_neg hc, hmw]
      rfl
  rw [hmw, hmwF, ← linkage_depth_eq_sum_difference P.Nr (kc P) (W.j τ) P.t (W.q τ) hrows (W.lam τ) w (D.U (inc τ))
    (D.U' (inc τ)) (hU τ) hU'] at hDB
  have hle := depth_nat_le_holds P ι W l τ (by linarith [one_le_h P hH]) hl.one_le
  have hle' : ((W.q τ * h0 P + (l * W.mwF P τ l + W.mw P τ l) * (P.t + 2 * (h0 P / (l - 1))) : ℕ) : ℤ) ≤
      (W.iW P l τ : ℤ) := by exact_mod_cast hle
  refine le_trans ?_ hle'
  unfold depthAt
  push_cast
  exact hDB

theorem first_input_of_link : FirstInputOfLink := by
  intro P hH hL ι W hW l X hl hlJ ϖ Λ L _ _ _ _ _ hwt h μ h1 h2 τ hτ
  exact depth_of_linkage_holds P hH hL ι W hW l hl hlJ τ (hwt μ τ) (h μ h1 h2 τ hτ)

theorem weight_inputs_of_linkage_holds : WInputsOfLink := by
  intro P hH hL ι _ W hW l X hl hlJ h
  obtain ⟨ϖ, n₀, e, Λ, L, i1, i2, i3, i4, i5, hwt, hfin, hϖ, hA, hT, hS, hK⟩ := h
  exact ⟨ϖ, n₀, e, Λ, L, i1, i2, i3, i4, i5, hwt, hfin, hϖ, hA, hT, hS,
    first_input_of_link P hH hL ι W hW l X hl hlJ ϖ Λ L hwt hK⟩

theorem coarse_le_c_w_holds : CoarseLeCW := by
  intro P hH hL ι W hW J τ hτ l hl
  have hdep0 := sizeData_depth_nonneg W P hH J τ l
  have hdep : (W.iW P l τ : ℝ) ≤ (W.sizeData₂ P J).depth P τ l :=
    Nat.floor_le (sizeData_depth_nonneg W P hH (fun _ => 0) τ l)
  have hi0 : (0 : ℝ) ≤ (W.iW P l τ : ℝ) := Nat.cast_nonneg _
  rw [correction_weight_eq_formula]
  unfold cCoarse
  obtain ⟨dep, hd⟩ : ∃ d, d = (W.sizeData₂ P J).depth P τ l := ⟨_, rfl⟩
  rw [← hd] at hdep hdep0 ⊢
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by linarith
  have hh0 := floor_height_le_height P hH
  have hk := kc_cast_le_k P
  have hw := hW.window τ
  have t1 : ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * (((h0 P : ℝ) + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6) ≤
      ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := div_le_div_of_nonneg_right (show (h0 P : ℝ) + (P.Nr : ℝ) ≤ P.h + (P.Nr : ℝ) by linarith) hl1
    linarith
  have hS : ((W.xp τ - W.xm τ : ℤ) : ℝ) ≤ P.S := by
    push_cast
    linarith [hw.1, hw.2.2]
  have hS0 : (0 : ℝ) ≤ ((W.xp τ - W.xm τ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hw.2.1
  have hIl := indexIntegral_nonneg_of_params l (W.xm τ) (W.xp τ) (W.top P τ)
  have t3 : (kc P : ℝ) * (((W.xp τ - W.xm τ : ℤ) : ℝ) / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ)) ≤
      (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ)) :=
    mul_le_mul hk (by linarith [div_le_div_of_nonneg_right hS hl0])
      (add_nonneg (div_nonneg hS0 hl0) hIl) (Nat.cast_nonneg _)
  have t4 : (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
        min (min (kc P : ℝ) (P.t : ℝ)) ((W.iW P l τ : ℝ) / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0) ≤
      (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
        min (min (P.k : ℝ) (P.t : ℝ)) (dep / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0) := by
    split_ifs
    · exact min_le_min (min_le_min hk le_rfl) (div_le_div_of_nonneg_right hdep (Nat.cast_nonneg _))
    · exact le_rfl
  have t5 : ((W.iW P l τ : ℝ) / (l : ℝ)) * (1 + Real.posLog ((h0 P : ℝ) / (l : ℝ))) ≤
      (dep / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by
    have hp : Real.posLog ((h0 P : ℝ) / (l : ℝ)) ≤ max 0 (Real.log (P.h / (l : ℝ))) :=
      Real.posLog_le_posLog (div_nonneg (Nat.cast_nonneg _) hl0) (div_le_div_of_nonneg_right hh0 hl0)
    exact mul_le_mul (div_le_div_of_nonneg_right hdep hl0) (by linarith)
      (add_nonneg zero_le_one Real.posLog_nonneg) (div_nonneg hdep0 hl0)
  by_cases hc : ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ
  · simp only [if_pos hc] at t4 ⊢
    linarith
  · simp only [if_neg hc] at t4 ⊢
    linarith

theorem j_w_seven_le_holds : CoarseWeightBoundLe := by
  intro P hH hL ι _ _ W hW J l hl
  constructor
  · unfold Wts.JW Wts.coarseWeightBound
    apply Finset.sum_le_sum
    intro τ _
    unfold cTau
    split_ifs
    · exact min_le_min le_rfl (Nat.floor_le_floor (short_bound_le_coarse_holds _ _ _ _ _ _ _ _ _ _ _ _).2)
    · exact le_rfl
  · unfold Wts.coarseWeightBound
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro τ _
    by_cases hτ : τ ∈ W.T2
    · have hτ' : τ ∈ (W.sizeData₂ P J).T2 := hτ
      rw [if_pos hτ']
      unfold cTau
      rw [if_pos hτ, Nat.cast_min]
      apply min_le_min le_rfl
      have h1 := coarse_le_c_w_holds P hH hL ι W hW J τ hτ l hl
      have h2 := short_bound_nonneg_holds l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ)
        (W.xp τ) (W.top P τ) (W.iW P l τ : ℝ) (by omega) (hW.window τ).2.1 (Nat.cast_nonneg _)
      have h3 := (short_bound_le_coarse_holds l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ)
        (W.xp τ) (W.top P τ) (W.iW P l τ : ℝ)).2
      exact (Nat.floor_le (h2.trans h3)).trans h1
    · have hτ' : τ ∉ (W.sizeData₂ P J).T2 := hτ
      rw [if_neg hτ']
      unfold cTau
      rw [if_neg hτ]
      exact le_rfl

theorem inclusion_w_seven_real_holds : HidaLatticeInclusionAtCoarseWeightBound := by
  intro hD P hH hL ι _ _ W hW l X hl hu hlJ hWI
  obtain ⟨ϖ, n₀, e, Λ, L, _, _, _, _, _, hwt, hfin, hϖ, hA, hT, hS, hI⟩ := hWI
  have hTop := top_inputs_real_holds P hH hL ι W hW l X hl hu hlJ ϖ n₀ e Λ L hwt hfin hϖ hA hT hS hI
  have h := weight_theorem_top_coarse (last_graded_of_graded_alone hD) X.O X.A X.G X.Γ X.K X.jK ι l
    P.Nr (kc P) P.t (h0 P) W.lam W.T2 W.j W.q W.xm W.xp (fun τ => W.ecl P τ l)
    (fun τ => W.ex P τ l) (W.iW P l) X.T X.S ϖ n₀ e Λ L hwt hTop
  exact ⟨h, Nat.sInf_le h⟩

theorem seventh_recursion_eq_a_of_small_prime {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (l : ℕ)
    (hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) : W.Jrec7 P l = W.JA P l := by
  rw [Wts.Jrec7, if_pos hc]

theorem seventh_recursion_eq_w_of_large_prime {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (l : ℕ)
    (hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp)) : W.Jrec7 P l = W.coarseWeightBound P l := by
  rw [Wts.Jrec7, if_neg hc]

theorem sizeData_boundW_of_le_seventh_recursion {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (hH : P.Hyp)
    (hL : P.Large) (hW : W.Ok P) (J : ℕ → ℕ) (hJ : ∀ l : ℕ, l.Prime → J l ≤ W.Jrec7 P l) :
    (W.sizeData₂ P J).BoundW P := by
  intro l hl hlJ hE hS _ _ _
  have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) :=
    not_or.mpr ⟨not_le.mpr hlJ, not_or.mpr ⟨hE, hS⟩⟩
  have h1 := hJ l hl
  rw [seventh_recursion_eq_w_of_large_prime W P l hc] at h1
  have h2 := (j_w_seven_le_holds P hH hL ι W hW J l hl.two_le).2
  have h3 : (J l : ℝ) ≤ (W.coarseWeightBound P l : ℝ) := by exact_mod_cast h1
  refine (h3.trans h2).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro τ _
  by_cases hτ : τ ∈ (W.sizeData₂ P J).T2
  · rw [if_pos hτ, if_pos hτ]
  · rw [if_neg hτ, if_neg hτ]

end Formalism.CohomologicalDescent.ShortWeightBounds
