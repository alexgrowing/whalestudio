import Formalism.LocalToGlobal.GlobalTheory.VandNHcSeqEq

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColOpen

open Formalism.BasicNotions Formalism.L2.Col Formalism.LogVandermondeBounds.StandardLattice Formalism.HermitianLattices.FormalDegreeBoundsAlt Formalism.HermitianLatticesTheory Finset

variable {X : Fields} {Pr : Primes X} {R : Ranks}

section Shape

variable {W : Wts X Pr.Word R} {Δ S a b' : ℝ} {c : X.Tau → ℝ} {code : Pr.Word → ℕ → ℕ}

theorem hcSeq_apply (W : Wts X Pr.Word R) (u : Pr.Word) (τ : X.Tau) (i : Fin R.k) :
    hcSeq W u τ i.1 = (((W.hc u τ).u i : ℚ) : ℝ) := by
  unfold hcSeq
  rw [dif_pos i.2]

theorem k_ge_real (R : Ranks) : (5 : ℝ) ≤ (R.k : ℝ) := by exact_mod_cast k_ge R

theorem Grid.S_pos (G : Grid W Δ S c code) : 0 < S := by
  rw [G.S_eq]
  have h1 := G.one_le_Δ
  have h2 := k_ge_real R
  positivity

theorem Grid.cloud_ge (G : Grid W Δ S c code) (τ : X.Tau) {l : ℕ} (hl : l < R.k - 2) : 4 * Δ ≤ vSeq W τ l := by
  have hk := k_ge R
  have h1 := G.cloud τ l (by omega)
  have h2 := G.cloud τ (R.k - 2) (by omega)
  have h3 := G.cloud_nonneg τ (R.k - 2) (by omega)
  have hΔ := G.one_le_Δ
  unfold cloudV at h1 h2
  have h4 : (l : ℝ) + 1 ≤ ((R.k - 2 : ℕ) : ℝ) := by exact_mod_cast hl
  have h5 : 4 * Δ * ((l : ℝ) + 1) ≤ 4 * Δ * ((R.k - 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h4 (by linarith)
  linarith

theorem Grid.word_mem (G : Grid W Δ S c code) (u : Pr.Word) (τ : X.Tau) {l : ℕ} (hl : l < R.k - 2) :
    3 * Δ - 1 / 2 ≤ hcSeq W u τ (l + 1) ∧ hcSeq W u τ (l + 1) ≤ S := by
  have h1 := G.word u τ l hl
  have h2 := G.cloud_ge τ hl
  have h3 := G.cloud_le τ l (by omega)
  have hΔ := G.one_le_Δ
  have h4 : ((code u l : ℕ) : ℝ) ≤ 1 := by exact_mod_cast G.code_le u l
  have h5 : (0 : ℝ) ≤ ((code u l : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : ((code u l : ℕ) : ℝ) * Δ ≤ 1 * Δ := mul_le_mul_of_nonneg_right h4 (by linarith)
  have h7 : 0 ≤ ((code u l : ℕ) : ℝ) * Δ := mul_nonneg h5 (by linarith)
  constructor <;> linarith

theorem Ends.S_le_b' (G : Grid W Δ S c code) (E : Ends W a b' S) : 5 * S ≤ b' := by
  have h1 := E.kS_le
  have h2 := k_ge_real R
  have h3 := G.S_pos
  nlinarith

theorem Ends.a_ge (G : Grid W Δ S c code) (E : Ends W a b' S) : 40 * S ≤ a := by
  have h1 := E.S_le_b' G
  have h2 := E.b'_le
  linarith

theorem hcShape_of (G : Grid W Δ S c code) (E : Ends W a b' S) (u : Pr.Word) : HCShape W u a b' S where
  cloud τ i h0 h1 := by
    have h := G.word_mem u τ (l := i.1 - 1) (by omega)
    rw [show i.1 - 1 + 1 = i.1 by omega, hcSeq_apply] at h
    have hΔ := G.one_le_Δ
    exact ⟨by linarith [h.1], h.2⟩
  top τ hτ := by
    obtain ⟨h1, h2, h3, h4⟩ := E.top u τ hτ
    refine ⟨h1, ?_, h3, h4⟩
    have ha : 0 < a := by linarith [E.a_ge G, G.S_pos]
    have hk := k_ge_real R
    have h5 : 1 / (R.k : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have h6 : a * (1 + 1 / (R.k : ℝ)) ≤ a * 2 := mul_le_mul_of_nonneg_left (by linarith) ha.le
    linarith
  oth_last τ hτ := by
    have hk := k_ge R
    have h1 := E.oth_last u τ hτ
    have h2 := G.cloud_nonneg τ (R.k - 2) (by omega)
    have h3 := hcSeq_apply W u τ (kLast R)
    have h4 : (kLast R).1 = R.k - 1 := rfl
    rw [h4] at h3
    rw [← h3, h1]
    linarith
  oth_first τ hτ := by
    have hk := k_ge R
    have h1 := (E.oth_first u τ hτ).2
    have h2 := G.cloud_le τ 0 (by omega)
    have h3 := hcSeq_apply W u τ (kFirst R)
    have h4 : (kFirst R).1 = 0 := rfl
    rw [h4] at h3
    rw [← h3]
    linarith
  k_le := by
    rw [G.S_eq]
    have hΔ := G.one_le_Δ
    have hk := k_ge_real R
    nlinarith
  kS_le := E.kS_le

theorem vandVar_of (hW : W.Ok) (G : Grid W Δ S c code) (E : Ends W a b' S) (u u' : Pr.Word) (τ : X.Tau) :
    |Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u τ) R.k) - Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u' τ) R.k)| ≤
      (R.k : ℝ) * (1 + Real.log (R.k : ℝ)) + 2 := by
  have hk := k_ge R
  have hΔ := G.one_le_Δ
  have hS : 4 * (R.k : ℝ) * Δ = S := by rw [G.S_eq]; ring
  rw [vandN_hcSeq_eq G u τ, vandN_hcSeq_eq G u' τ, hcSeq_zero_eq hW u' u τ, hcSeq_last_eq hW u' u τ]
  refine explicit_variation_bound R.k (c τ) Δ _ _ (code u) (code u') (by omega) (by linarith) (G.code_le u) (G.code_le u') ?_ ?_
  · rw [← G.cloud τ 0 (by omega)]
    by_cases hτ : τ ∈ W.tops
    · have h1 := (E.top u τ hτ).1
      have h2 := G.cloud_le τ 0 (by omega)
      have h3 := E.a_ge G
      have h4 := G.S_pos
      have h5 := k_ge_real R
      rw [hcSeq_zero, hS]
      linarith
    · have h1 := (E.oth_first u τ hτ).1
      rw [hS]
      exact h1
  · by_cases hτ : τ ∈ W.tops
    · right
      intro l hl
      rw [← G.cloud τ l (by omega), hcSeq_last, hS]
      have h1 := (E.top u τ hτ).2.2.1
      have h2 := G.cloud_ge τ hl
      have h3 := E.S_le_b' G
      have h4 := G.S_pos
      have h5 := k_ge_real R
      linarith
    · left
      rw [← G.cloud τ (R.k - 2) (by omega)]
      exact E.oth_last u τ hτ

end Shape

section Fields1

variable {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m} {Δ : ℝ} {c : X.Tau → ℝ} {code : Pr.Word → ℕ → ℕ}

theorem wtWinZ_col (A : ColArg W Ch) (G : Grid W Δ A.num.Sc c code) (E : Ends W A.num.sc.a A.num.sc.b' A.num.Sc)
    (hC : 2 ≤ A.num.C0) : ∀ u, WtWin W u A.num.C0 A.num.sc.a A.num.sc.b' A.num.Sc :=
  fun u => wtWin_of_shape (hcShape_of G E u) hC

theorem vandVar_col {S a b' : ℝ} (hW : W.Ok) (G : Grid W Δ S c code) (E : Ends W a b' S) :
    ∀ u u' τ, |Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u τ) R.k) - Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u' τ) R.k)| ≤
      (R.k : ℝ) * (1 + Real.log (R.k : ℝ)) + 2 :=
  fun u u' τ => vandVar_of hW G E u u' τ

theorem weylDim_col (W : Wts X Pr.Word R) : ∀ u τ, WeylDim (W.lamTrue u 0 τ) := fun _ _ => weylDim_holds _

end Fields1

variable (X R) in

structure NumsZ (n : ScNum) (LL : ℝ) : Prop where
  window_constant_ge : 16 + 3 * n.CY ≤ n.C0
  eta_nonneg : 0 ≤ n.eta
  S_nonneg : 0 ≤ n.Sc
  small : n.Sc + n.eta + (R.m : ℝ) * R.t ≤ n.sc.b'
  pow : ((X.f : ℝ) * R.m * R.N R.m) ^ 3 * (1 + n.C0 * R.m + 2 * n.C0) * LL ≤ n.sc.b'

theorem scale_a_pos (sc : Scale) : 0 < sc.a := mul_pos (by linarith [sc.one_lt_alt]) (Real.exp_pos _)

theorem scale_b'_le_a (sc : Scale) : sc.b' ≤ sc.a := by
  unfold Scale.b'
  refine div_le_self (scale_a_pos sc).le ?_
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [sc.one_lt_alt]) _)

theorem log_av_eq (sc : Scale) {v : ℝ} (hv : 0 < v) : Real.log (sc.a * v) = Real.log sc.x + sc.L + Real.log v := by
  have hx := sc.one_lt_alt
  unfold Scale.a Scale.b
  rw [Real.log_mul (by have := Real.exp_pos sc.L; positivity) hv.ne', Real.log_mul (by linarith) (Real.exp_pos _).ne',
    Real.log_exp]

theorem L_le_log_av (sc : Scale) {v : ℝ} (hv : 1 ≤ v) : sc.L ≤ Real.log (sc.a * v) := by
  rw [log_av_eq sc (by linarith)]
  have h1 : 0 < Real.log sc.x := Real.log_pos sc.one_lt_alt
  have h2 : 0 ≤ Real.log v := Real.log_nonneg hv
  linarith

section Numbers

variable {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

theorem logT_le_of (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hfk : X.f ≤ R.k) (n : ScNum) {dsig : X.Tau → ℝ}
    (hd : ∀ τ, 0 < dsig τ) {Γ : ℝ} (hΓ : 1 ≤ Γ) (u : Pr.Word) (hT : InWindow W Ch dsig Γ u)
    (hup : Real.log (XuC W Ch dsig u) ≤ xUpC R n) : logTC Pr u ≤ (16 + 3 * n.CY) * R.m * n.sc.L := by
  have h := (level_window_col W Ch hX hPr hbig hfk u hd hΓ hT _ _ le_rfl hup).2.2.1
  have hL := one_lt_L n.sc
  have hm : (2 : ℝ) ≤ (R.m : ℝ) := by exact_mod_cast R.two_le_m
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h3 : (1 : ℝ) ≤ (R.m : ℝ) * n.sc.L := by nlinarith
  unfold logTC
  unfold xUpC at h
  nlinarith

theorem numbersZ_of (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hfk : X.f ≤ R.k) (n : ScNum) {LL : ℝ}
    (hLL : LL = Real.log (n.sc.a * vC X)) (N5 : Nums5 X Pr R n) (NZ : NumsZ X R n LL) {dsig : X.Tau → ℝ}
    (hd : ∀ τ, 0 < dsig τ) {Γ : ℝ} (hΓ : 1 ≤ Γ) (hT : ∀ u, InWindow W Ch dsig Γ u)
    (hup : ∀ u, Real.log (XuC W Ch dsig u) ≤ xUpC R n) :
    ∀ u, NumbersC Pr R u n.C0 n.sc.a n.sc.b' LL n.eta n.Sc := by
  intro u
  have hL0 := one_lt_L n.sc
  have hv : 1 ≤ vC X := by
    have := N5.pi_le_v
    have := Real.pi_gt_three
    linarith
  have hLle : n.sc.L ≤ LL := by
    rw [hLL]
    exact L_le_log_av n.sc hv
  have hLL1 : 1 ≤ LL := by linarith
  have hCY : 0 ≤ n.CY := by
    have h1 := N5.log_g 0
    have h2 : (0 : ℝ) ≤ Real.log (Pr.g 0) := Real.log_natCast_nonneg _
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith
  have hC0 : 16 ≤ n.C0 := by linarith [NZ.window_constant_ge]
  have hm : (2 : ℝ) ≤ (R.m : ℝ) := by exact_mod_cast R.two_le_m
  have hf : (1 : ℝ) ≤ (X.f : ℝ) := by exact_mod_cast iface_f_pos hX
  have hN : (2 : ℝ) ≤ (R.N R.m : ℝ) := by exact_mod_cast two_le_N R
  have hlogT0 : 0 ≤ logTC Pr u := Real.log_natCast_nonneg _

  have hTle : logTC Pr u ≤ n.C0 * R.m * LL := by
    have h1 := logT_le_of hX hPr hbig hfk n hd hΓ u (hT u) (hup u)
    have h2 : (16 + 3 * n.CY) * R.m * n.sc.L ≤ n.C0 * R.m * LL := by
      have h3 : (16 + 3 * n.CY) * R.m ≤ n.C0 * R.m := mul_le_mul_of_nonneg_right NZ.window_constant_ge (by linarith)
      exact mul_le_mul h3 hLle (by linarith) (by positivity)
    linarith

  have hgle : loggC Pr ≤ n.C0 * LL := by
    unfold loggC
    have hg : ∀ i, (0 : ℝ) < Pr.g i := fun i => by exact_mod_cast (hPr.g_prime i).pos
    rw [Real.log_mul (hg 0).ne' (hg 1).ne']
    have h1 := N5.log_g 0
    have h2 := N5.log_g 1
    have h3 : 2 * n.CY * n.sc.L ≤ n.C0 * LL :=
      mul_le_mul (by linarith [NZ.window_constant_ge]) hLle (by linarith) (by linarith)
    linarith

  set K : ℝ := ((X.f : ℝ) * R.m * R.N R.m) ^ 3 with hK
  have hKe : K = (X.f : ℝ) ^ 3 * (R.m : ℝ) ^ 3 * (R.N R.m : ℝ) ^ 3 := by rw [hK]; ring
  have hf3 : (1 : ℝ) ≤ (X.f : ℝ) ^ 3 := one_le_pow₀ hf
  have hm3 : (1 : ℝ) ≤ (R.m : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hN3 : (R.N R.m : ℝ) ≤ (R.N R.m : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hK1 : (R.m : ℝ) ^ 3 * R.N R.m ≤ K := by
    rw [hKe]
    calc (R.m : ℝ) ^ 3 * R.N R.m = 1 * (R.m : ℝ) ^ 3 * R.N R.m := by ring
      _ ≤ (X.f : ℝ) ^ 3 * (R.m : ℝ) ^ 3 * (R.N R.m : ℝ) ^ 3 := by gcongr
  have hK2 : (R.N R.m : ℝ) ≤ K := by
    refine le_trans ?_ hK1
    calc (R.N R.m : ℝ) = 1 * R.N R.m := by ring
      _ ≤ (R.m : ℝ) ^ 3 * R.N R.m := by gcongr
  have hpow := NZ.pow
  have hQ0 : 0 ≤ n.C0 * R.m := by positivity

  have hmain : (R.N R.m : ℝ) * ((1 + n.C0 * R.m) * LL) ≤ n.sc.b' := by
    refine le_trans ?_ hpow
    rw [mul_assoc]
    refine mul_le_mul hK2 ?_ (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hsum : LL + logTC Pr u ≤ (1 + n.C0 * R.m) * LL := by linarith
  refine numbersC_of Pr R u hLL1 hv (by rw [hLL]) ?_ (scale_b'_le_a n.sc) hTle hgle NZ.eta_nonneg NZ.S_nonneg NZ.small ?_ ?_ ?_
  · refine le_trans ?_ hmain
    have : (1 : ℝ) ≤ (1 + n.C0 * R.m) * LL := by nlinarith
    nlinarith
  · have h1 : (R.N R.m : ℝ) * (LL + logTC Pr u) ≤ n.sc.b' :=
      le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hmain
    calc (R.N R.m : ℝ) ^ 2 * (LL + logTC Pr u) = R.N R.m * ((R.N R.m : ℝ) * (LL + logTC Pr u)) := by ring
      _ ≤ R.N R.m * n.sc.b' := mul_le_mul_of_nonneg_left h1 (by linarith)
  · refine le_trans ?_ hmain
    have h1 : n.C0 * R.m * LL ≤ (R.N R.m : ℝ) * (n.C0 * R.m * LL) := by
      have : 0 ≤ n.C0 * R.m * LL := by positivity
      nlinarith
    nlinarith
  · refine le_trans ?_ hpow
    have h1 : (1 + 2 * n.C0) * ((R.m : ℝ) ^ 3 * R.N R.m) ≤ (1 + n.C0 * R.m + 2 * n.C0) * K :=
      mul_le_mul (by linarith) hK1 (by positivity) (by linarith)
    have h2 : (1 + n.C0 * R.m + 2 * n.C0) * K ≤ (1 + n.C0 * R.m + 2 * n.C0) * K * LL := by
      have : 0 ≤ (1 + n.C0 * R.m + 2 * n.C0) * K := by
        have : 0 ≤ K := by linarith
        positivity
      nlinarith
    calc (1 + 2 * n.C0) * (R.m : ℝ) ^ 3 * R.N R.m = (1 + 2 * n.C0) * ((R.m : ℝ) ^ 3 * R.N R.m) := by ring
      _ ≤ (1 + n.C0 * R.m + 2 * n.C0) * K * LL := le_trans h1 h2
      _ = K * (1 + n.C0 * R.m + 2 * n.C0) * LL := by ring

theorem numbersZ_col (hX : X.Ok) (hPr : Pr.Ok) (A : ColArg W Ch) (hS : Sizes Pr W A.num.sc.a) (hfk : X.f ≤ R.k)
    (N5 : Nums5 X Pr R A.num) (NZ : NumsZ X R A.num (logAvC X A.num)) (hd : ∀ τ, 0 < A.dsig τ) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hT : ∀ u, InWindow W Ch A.dsig Γ u) (hup : ∀ u, Real.log (XuC W Ch A.dsig u) ≤ xUpC R A.num) :
    ∀ u, NumbersC Pr R u A.num.C0 A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.eta A.num.Sc :=
  numbersZ_of hX hPr (hS.g_big 0) hfk A.num rfl N5 NZ hd hΓ hT hup

theorem window_constant_ge_sixteen (n : ScNum) {LL : ℝ} (N5 : Nums5 X Pr R n) (NZ : NumsZ X R n LL) : 16 ≤ n.C0 := by
  have hL0 := one_lt_L n.sc
  have h1 := N5.log_g 0
  have h2 : (0 : ℝ) ≤ Real.log (Pr.g 0) := Real.log_natCast_nonneg _
  have hCY : 0 ≤ n.CY := by
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith
  linarith [NZ.window_constant_ge]

example (hX : X.Ok) (hPr : Pr.Ok) (hW : W.Ok) (A : ColArg W Ch) (hS : Sizes Pr W A.num.sc.a) (hfk : X.f ≤ R.k)
    {Δ : ℝ} {c : X.Tau → ℝ} {code : Pr.Word → ℕ → ℕ} (G : Grid W Δ A.num.Sc c code) (E : Ends W A.num.sc.a A.num.sc.b' A.num.Sc)
    (N5 : Nums5 X Pr R A.num) (NZ : NumsZ X R A.num (logAvC X A.num)) (hd : ∀ τ, 0 < A.dsig τ) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hT : ∀ u, InWindow W Ch A.dsig Γ u) (h : ColOpen W Ch A) : ColOpen W Ch A :=
  { h with
    weightConst_nonneg := by linarith [window_constant_ge_sixteen A.num N5 NZ]
    numbersZ := numbersZ_col hX hPr A hS hfk N5 NZ hd hΓ hT h.log_height_upper_bound
    wtWinZ := wtWinZ_col A G E (by linarith [window_constant_ge_sixteen A.num N5 NZ])
    weylDim := weylDim_col W
    vandVar := vandVar_col hW G E }

end Numbers

end Formalism.L2.GlobalTheoryTheory.ColOpen
