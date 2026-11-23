import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open Complex

namespace GlobalTheory.CompanionTheory.EisensteinPoissonSummation

theorem ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by ring⟩

theorem norm_ee_real (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * I * t) = ((2 * Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem GS_norm_le (r : ℤ) (d : ℕ) : ‖GS r d‖ ≤ d := by
  unfold GS
  calc ‖∑ x ∈ Finset.range d, ee (r * (x : ℂ) ^ 2 / d)‖
      ≤ ∑ x ∈ Finset.range d, ‖ee (r * (x : ℂ) ^ 2 / d)‖ := norm_sum_le _ _
    _ = ∑ x ∈ Finset.range d, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have : (r : ℂ) * (x : ℂ) ^ 2 / d = (((r : ℝ) * (x : ℝ) ^ 2 / d : ℝ) : ℂ) := by push_cast; rfl
        rw [this, norm_ee_real]
    _ = d := by simp

theorem GS_add (r j : ℤ) (d : ℕ) (hd : 0 < d) : GS (r + j * d) d = GS r d := by
  unfold GS
  refine Finset.sum_congr rfl fun x _ => ?_
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (((r + j * d : ℤ)) : ℂ) * (x : ℂ) ^ 2 / d = (r : ℂ) * (x : ℂ) ^ 2 / d + ((j * (x : ℤ) ^ 2 : ℤ) : ℂ) := by
    push_cast; field_simp
  rw [this, ee_add, ee_int, mul_one]

theorem RR_norm_le (n : ℤ) (d : ℕ) : ‖RR n d‖ ≤ (d : ℝ) ^ 2 := by
  unfold RR
  calc ‖∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), GS r d * ee (-(n * r / d))‖
      ≤ ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), ‖GS r d * ee (-(n * r / d))‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), (d : ℝ) := by
        refine Finset.sum_le_sum fun r _ => ?_
        have : (-((n : ℂ) * r / d)) = ((-((n : ℝ) * r / d) : ℝ) : ℂ) := by push_cast; rfl
        rw [norm_mul, this, norm_ee_real, mul_one]
        exact GS_norm_le _ _
    _ = ((Finset.range d).filter (fun r => Nat.Coprime r d)).card * (d : ℝ) := by simp
    _ ≤ (d : ℝ) * d := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    _ = (d : ℝ) ^ 2 := by ring

theorem swap (b : ℕ → ℂ) (Q : ℤ → ℂ) (hb : Summable fun d : ℕ => ‖b d‖ * (d : ℝ) ^ 2)
    (hQ : Summable fun n : ℤ => ‖Q n‖) :
    ∑' d : ℕ, b d * ∑' n : ℤ, RR n d * Q n = ∑' n : ℤ, (∑' d : ℕ, b d * RR n d) * Q n := by
  have hS : Summable (Function.uncurry fun (d : ℕ) (n : ℤ) => b d * (RR n d * Q n)) := by
    refine Summable.of_norm_bounded (hb.mul_of_nonneg hQ (fun _ => by positivity) (fun _ => norm_nonneg _)) ?_
    rintro ⟨d, n⟩
    simp only [Function.uncurry, norm_mul]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (RR_norm_le n d) (norm_nonneg _)
  calc ∑' d : ℕ, b d * ∑' n : ℤ, RR n d * Q n
      = ∑' d : ℕ, ∑' n : ℤ, b d * (RR n d * Q n) := tsum_congr fun d => tsum_mul_left.symm
    _ = ∑' n : ℤ, ∑' d : ℕ, b d * (RR n d * Q n) := hS.tsum_comm.symm
    _ = ∑' n : ℤ, (∑' d : ℕ, b d * RR n d) * Q n := by
        refine tsum_congr fun n => ?_
        rw [← tsum_mul_right]
        exact tsum_congr fun d => by ring

theorem coef_summable (M : ℕ) [NeZero M] (c : DirichletCharacter ℂ M) (s : ℂ) (hs : 2 < s.re) :
    Summable fun d : ℕ => ‖c (d : ZMod M) * (d : ℂ) ^ (-(s + 1))‖ * (d : ℝ) ^ 2 := by
  have h0 : Summable fun d : ℕ => (d : ℝ) ^ (1 - s.re) := Real.summable_nat_rpow.2 (by linarith)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun d => ?_) h0
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero]
    rw [zero_pow two_ne_zero, mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd]
    have h1 : ‖c (d : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one c _
    have h2 : (d : ℝ) ^ (1 - s.re) = (d : ℝ) ^ (-(s + 1)).re * (d : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_add hd']
      congr 1
      simp; ring
    rw [h2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ‖c (d : ZMod M)‖ * (d : ℝ) ^ (-(s + 1)).re ≤ 1 * (d : ℝ) ^ (-(s + 1)).re :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _

theorem idx_tsum (M : ℕ) (hM : 2 ∣ M) (hM0 : M ≠ 0) (b : ℕ → ℂ) (G : ℕ → ℤ → ℂ) (B : ℝ)
    (hb0 : ∀ d : ℕ, ¬ Nat.Coprime d M → b d = 0)
    (hbs : Summable fun d : ℕ => ‖b d‖ * (d : ℝ) ^ 2)
    (hG : ∀ d : ℕ, 0 < d →
      (Summable fun c' : ℤ => ‖if IsCoprime c' (d : ℤ) then G d c' else 0‖) ∧
      ∑' c' : ℤ, ‖if IsCoprime c' (d : ℤ) then G d c' else 0‖ ≤ (d : ℝ) ^ 2 * B) :
    ∑' p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2 =
      ∑' d : ℕ, b d * ∑' c' : ℤ, if IsCoprime c' (d : ℤ) then G d c' else 0 := by
  classical
  have hM1 : ¬ Nat.Coprime 0 M := by
    intro h
    have h1 : M = 1 := by simpa using h
    subst h1
    norm_num at hM
  have hb00 : b 0 = 0 := hb0 0 hM1
  let A : ℕ → ℤ → ℂ := fun d c' => if IsCoprime c' (d : ℤ) then G d c' else 0
  let F : ℕ × ℤ → ℂ := fun p => b p.1 * A p.1 p.2
  have hnorm : ∀ p, ‖F p‖ = ‖b p.1‖ * ‖A p.1 p.2‖ := fun p => norm_mul _ _
  have hsF : Summable fun p => ‖F p‖ := by
    refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun d => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp only [hnorm, hb00, norm_zero, zero_mul]
        exact summable_zero
      · simp only [hnorm]
        exact (hG d hd).1.mul_left _
    · refine Summable.of_nonneg_of_le (fun d => tsum_nonneg fun _ => norm_nonneg _) (fun d => ?_)
        (hbs.mul_right B)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [hnorm, hb00]
      · simp only [hnorm]
        rw [tsum_mul_left, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hG d hd).2 (norm_nonneg _)
  have hsupp : Function.support F ⊆
      {p : ℕ × ℤ | 0 < p.1 ∧ IsCoprime (((4 * M ^ 2 : ℕ) : ℤ) * p.2) (p.1 : ℤ)} := by
    rintro ⟨d, c'⟩ hp
    have h1 : b d ≠ 0 := left_ne_zero_of_mul hp
    have h2 : IsCoprime c' (d : ℤ) := by
      by_contra h
      apply hp
      simp [F, A, h]
    have hc : Nat.Coprime d M := by
      by_contra h
      exact h1 (hb0 d h)
    have hpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd hc hM1
      · exact h
    have hodd : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right hM hc
    have h4 : Nat.Coprime 4 d := by
      have := (hodd.pow_right 2).symm
      simpa using this
    have hc4 : Nat.Coprime (4 * M ^ 2) d := Nat.Coprime.mul_left h4 (hc.symm.pow_left 2)
    exact ⟨hpos, IsCoprime.mul_left (Nat.isCoprime_iff_coprime.2 hc4) h2⟩
  have hback : ∀ p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2 = F p.1 := by
    intro p
    have : IsCoprime p.1.2 (p.1.1 : ℤ) := IsCoprime.of_mul_left_right p.2.2
    simp [F, A, this]
  calc ∑' p : Idx (4 * M ^ 2), b p.1.1 * G p.1.1 p.1.2
      = ∑' p : Idx (4 * M ^ 2), F p.1 := tsum_congr hback
    _ = ∑' p : ℕ × ℤ, F p := tsum_subtype_eq_of_support_subset hsupp
    _ = ∑' d : ℕ, ∑' c' : ℤ, F (d, c') := hsF.of_norm.tsum_prod
    _ = ∑' d : ℕ, b d * ∑' c' : ℤ, if IsCoprime c' (d : ℤ) then G d c' else 0 :=
        tsum_congr fun d => by
          simp only [F, A]
          exact tsum_mul_left

theorem inner (K : ℝ → ℂ) (Ph : ℤ → ℂ) (Y : ℂ) (C x : ℝ)
    (h1 : ∀ t : ℝ, (Summable fun j : ℤ => ‖K (t - j)‖) ∧ ∑' j : ℤ, ‖K (t - j)‖ ≤ C)
    (h2 : Summable fun n : ℤ => ‖Ph n‖)
    (h3 : ∀ t : ℝ, ∑' j : ℤ, K (t - j) = ∑' n : ℤ, Y * Ph n * ee (n * t))
    (d : ℕ) (hd : 0 < d) :
    (Summable fun c' : ℤ => ‖if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0‖) ∧
    (∑' c' : ℤ, ‖if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0‖ ≤ (d : ℝ) ^ 2 * C) ∧
    ∑' c' : ℤ, (if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0) =
      ∑' n : ℤ, RR n d * (Y * Ph n * ee (n * x)) := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hC0 : 0 ≤ C := le_trans (tsum_nonneg fun _ => norm_nonneg _) (h1 0).2
  let A : ℤ → ℂ := fun c' => if IsCoprime c' (d : ℤ) then GS c' d * K (x - c' / d) else 0
  let e : Fin d × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv d).symm
  have he : ∀ p : Fin d × ℤ, e p = p.2 * d + ((p.1 : ℕ) : ℤ) := fun p => by
    simp [e, Int.divModEquiv_symm_apply]
  let t : Fin d → ℝ := fun r => x - ((r : ℕ) : ℝ) / d
  let g : Fin d → ℂ := fun r => if Nat.Coprime r d then GS ((r : ℕ) : ℤ) d else 0
  have hAe : ∀ (r : Fin d) (j : ℤ), A (e (r, j)) = g r * K (t r - j) := by
    intro r j
    have hcop : IsCoprime (j * d + ((r : ℕ) : ℤ)) (d : ℤ) ↔ Nat.Coprime r d := by
      rw [add_comm, IsCoprime.add_mul_right_left_iff, Nat.isCoprime_iff_coprime]
    simp only [A, he, g, t]
    by_cases h : Nat.Coprime r d
    · rw [if_pos (hcop.2 h), if_pos h, add_comm (j * (d : ℤ)), GS_add _ _ _ hd]
      congr 2
      push_cast
      field_simp
      ring
    · rw [if_neg (fun h' => h (hcop.1 h')), if_neg h, zero_mul]
  have hg : ∀ r, ‖g r‖ ≤ d := by
    intro r
    simp only [g]
    split_ifs
    · exact GS_norm_le _ _
    · simp
  have hfib : ∀ r : Fin d, Summable fun j : ℤ => ‖A (e (r, j))‖ := by
    intro r
    simp only [hAe, norm_mul]
    exact (h1 (t r)).1.mul_left _
  have hfibs : ∀ r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ ≤ d * C := by
    intro r
    simp only [hAe, norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul (hg r) (h1 (t r)).2 (tsum_nonneg fun _ => norm_nonneg _) (Nat.cast_nonneg _)
  have hsum : Summable fun p : Fin d × ℤ => ‖A (e p)‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hfib, (hasSum_fintype _).summable⟩
  have hs1 : Summable fun c' => ‖A c'‖ := e.summable_iff.1 hsum
  refine ⟨hs1, ?_, ?_⟩
  · calc ∑' c' : ℤ, ‖A c'‖ = ∑' p : Fin d × ℤ, ‖A (e p)‖ := (e.tsum_eq fun c' => ‖A c'‖).symm
      _ = ∑' r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ := hsum.tsum_prod
      _ = ∑ r : Fin d, ∑' j : ℤ, ‖A (e (r, j))‖ := tsum_fintype _
      _ ≤ ∑ _r : Fin d, (d : ℝ) * C := Finset.sum_le_sum fun r _ => hfibs r
      _ = (d : ℝ) ^ 2 * C := by simp; ring
  · have hsumA : Summable fun p : Fin d × ℤ => A (e p) := hsum.of_norm
    have hee : ∀ (n : ℤ) (r : Fin d), ee (n * (t r : ℝ)) = ee (-(n * ((r : ℕ) : ℂ) / d)) * ee (n * x) := by
      intro n r
      rw [← ee_add]
      congr 1
      simp only [t]
      push_cast
      ring
    have hQs : ∀ r : Fin d, Summable fun n : ℤ => g r * (Y * Ph n * ee (n * (t r : ℝ))) := by
      intro r
      refine Summable.mul_left _ (Summable.of_norm ?_)
      have hn : ∀ n : ℤ, ‖ee (n * (t r : ℝ))‖ = 1 := by
        intro n
        have : (n : ℂ) * (t r : ℝ) = (((n : ℝ) * t r : ℝ) : ℂ) := by push_cast; rfl
        rw [this, norm_ee_real]
      simp only [norm_mul, hn, mul_one]
      exact h2.mul_left _
    calc ∑' c' : ℤ, A c' = ∑' p : Fin d × ℤ, A (e p) := (e.tsum_eq A).symm
      _ = ∑' r : Fin d, ∑' j : ℤ, A (e (r, j)) := hsumA.tsum_prod
      _ = ∑ r : Fin d, ∑' j : ℤ, A (e (r, j)) := tsum_fintype _
      _ = ∑ r : Fin d, ∑' n : ℤ, g r * (Y * Ph n * ee (n * (t r : ℝ))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [hAe]
          rw [tsum_mul_left, tsum_mul_left, h3]
      _ = ∑' n : ℤ, ∑ r : Fin d, g r * (Y * Ph n * ee (n * (t r : ℝ))) :=
          (Summable.tsum_finsetSum fun r _ => hQs r).symm
      _ = ∑' n : ℤ, RR n d * (Y * Ph n * ee (n * x)) := by
          refine tsum_congr fun n => ?_
          unfold RR
          rw [Finset.sum_filter, Finset.sum_range, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [g]
          by_cases h : Nat.Coprime r d
          · rw [if_pos h, if_pos h, hee]
            ring
          · rw [if_neg h, if_neg h, zero_mul, zero_mul]

theorem eisenstein_cusp_zero_fourier_expansion : P1 → P2 := by
  intro hP1 M k ν _ h2 c s v hs hv
  have hM0 : M ≠ 0 := NeZero.ne M
  set y := v.im with hy
  set x := v.re with hx
  set α := al k ν s with hα
  set β := be k ν s with hβ
  have ha : α = s / 2 + (((ν : ℝ) + 1 - k) / 2 : ℝ) := by
    simp only [hα, al]; push_cast; ring
  have hb : β = s / 2 + (((k : ℝ) - ν) / 2 : ℝ) := by
    simp only [hβ, be]; push_cast; ring
  have hsum : α + β = s + 1 / 2 := by rw [ha, hb]; push_cast; ring
  have hre : 1 < (α + β).re := by
    rw [hsum]; simp; linarith
  obtain ⟨⟨C, hC⟩, hPh, hPo⟩ := hP1 s α β _ _ y ha hb hre hv
  have hY : (y : ℂ) ^ (1 - α - β) = (y : ℂ) ^ (1 / 2 - s) := by
    congr 1; linear_combination -hsum
  set Y : ℂ := (y : ℂ) ^ (1 / 2 - s) with hYd
  have hPo' : ∀ t : ℝ, ∑' j : ℤ, KK α β y (t - j) = ∑' n : ℤ, Y * Phi α β (n * y) * ee (n * t) := by
    intro t; rw [hPo t, hY]
  have hin := inner (KK α β y) (fun n => Phi α β (n * y)) Y C x hC hPh hPo'
  have hcs := coef_summable M c s hs
  have hb0 : ∀ d : ℕ, ¬ Nat.Coprime d M → c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) = 0 := by
    intro d hd
    rw [MulChar.map_nonunit c (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
  have hidx := idx_tsum M h2 hM0 (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)))
    (fun d c' => GS c' d * KK α β y (x - c' / d)) C hb0 hcs
    (fun d hd => ⟨(hin d hd).1, (hin d hd).2.1⟩)
  have hQ : Summable fun n : ℤ => ‖Y * Phi α β (n * y) * ee (n * x)‖ := by
    have hn : ∀ n : ℤ, ‖ee (n * x)‖ = 1 := by
      intro n
      simp only [ee]
      have : (2 * (Real.pi : ℂ) * I * (n * x)) = ((2 * Real.pi * n * x : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    simp only [norm_mul, hn, mul_one]
    exact hPh.mul_left _
  have hsw := swap (fun d => c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)))
    (fun n => Y * Phi α β (n * y) * ee (n * x)) hcs hQ
  have hE : Ep c k ν s v = ∑' p : Idx (4 * M ^ 2), (c (p.1.1 : ZMod M) * (p.1.1 : ℂ) ^ (-(s + 1))) *
      (GS p.1.2 p.1.1 * KK α β y (x - p.1.2 / p.1.1)) := by
    unfold Ep tm
    refine tsum_congr fun p => ?_
    ring
  rw [hE, hidx]
  have h1 : ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) *
      (∑' c' : ℤ, if IsCoprime c' (d : ℤ) then GS c' d * KK α β y (x - c' / d) else 0) =
      c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * ∑' n : ℤ, RR n d * (Y * Phi α β (n * y) * ee (n * x)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ¬ Nat.Coprime 0 M := by
        intro h
        have : M = 1 := by simpa using h
        subst this
        simp at h2
      rw [hb0 0 this, zero_mul, zero_mul]
    · rw [(hin d hd).2.2]
  rw [tsum_congr h1, hsw]
  refine tsum_congr fun n => ?_
  unfold Dn
  have : ∀ d : ℕ, c (d : ZMod M) * (d : ℂ) ^ (-(s + 1)) * RR n d = c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1)) := by
    intro d; ring
  rw [tsum_congr this]
  ring

end GlobalTheory.CompanionTheory.EisensteinPoissonSummation
