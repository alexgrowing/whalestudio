import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenGapCoefStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalSectionBoundsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpqRepVocabularyAgree
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bpNear_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    2 * ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) + ThreeDimData.AG k r + 3 ≤
        31 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * ThreeDimData.AG k r + 3 ≤
        24 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
        2 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      1 ≤ ((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * r + k + 1 := by push_cast; ring
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set s : ℝ := (r : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by linarith
  have hn1 : 1 ≤ n := by linarith
  have key : ∀ i j : ℕ, i ≤ 4 → j ≤ 3 → s ^ i * n ^ j ≤ s ^ 4 * n ^ 3 := fun i j hi hj =>
    mul_le_mul (pow_le_pow_right₀ hs1 hi) (pow_le_pow_right₀ hn1 hj) (by positivity) (by positivity)
  have hM : ThreeDimData.Mexp r ≤ 2 * s ^ 2 := by unfold ThreeDimData.Mexp; rw [hs]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n * s := by
    unfold ThreeDimData.AG; rw [← hs]
    have : (k : ℝ) + r ≤ n := by linarith
    nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ 2 * s * n := by unfold ThreeDimData.dN; rw [hs, hn]; nlinarith [mul_nonneg hr hr]
  have hd0 : 0 ≤ ThreeDimData.dN k r := by unfold ThreeDimData.dN; nlinarith [mul_nonneg hr hr, mul_nonneg hr (by linarith : (0 : ℝ) ≤ k)]
  have hS : ThreeDimData.AS k r ≤ n * (2 * s * n) := by
    unfold ThreeDimData.AS
    refine mul_le_mul ?_ hd hd0 (by linarith)
    rw [hn]; push_cast; linarith
  have hS0 : 0 ≤ ThreeDimData.AS k r := by unfold ThreeDimData.AS; positivity
  have hP : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 2 * s ^ 2 * (n * (2 * s * n) + 4 * n * s) :=
    mul_le_mul hM (by linarith) (by linarith) (by positivity)
  have k32 := key 3 2 (by omega) (by omega)
  have k31 := key 3 1 (by omega) (by omega)
  have k11 := key 1 1 (by omega) (by omega)
  have k12 := key 1 2 (by omega) (by omega)
  have k20 := key 2 0 (by omega) (by omega)
  have k00 := key 0 0 (by omega) (by omega)
  have hrn : s ^ 2 * (r * n) ≤ s ^ 3 * n ^ 1 := by
    have : (r : ℝ) * n ≤ s * n := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc s ^ 2 * (r * n) ≤ s ^ 2 * (s * n) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = s ^ 3 * n ^ 1 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · simpa using k00

theorem bpNear_gapOK (k r : ℕ) (hk : 1 ≤ k) (c Cg : ℝ) (hC : 240 + 2 * |c| ≤ Cg) :
    ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) ∧
    c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ThreeDimData.aOf r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := bpNear_thresholds k r hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hc : 0 ≤ |c| := abs_nonneg c
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hm]
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set N : ℝ := ((3 * (r + 1) : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ 2 * ((r : ℝ) + 1) := by linarith
  have hpos : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by linarith
  have hsq : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.2 hpos
  have hpow : (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) =
      (2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_natCast]
  have hge : 1 ≤ (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) := Real.one_le_rpow hs1 (by norm_num)
  have hZ : n ^ 3 ≤ N * n ^ 2 + n ^ 3 := by have : 0 ≤ N * n ^ 2 := by positivity
                                            linarith
  have hCg : 0 ≤ Cg := by linarith
  have ha : Cg * (((r : ℝ) + 1) ^ 4 * n ^ 3) ≤
      ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) := by
    have e : ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) =
        Cg * (((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) := by
      unfold ThreeDimData.aOf; rw [hpow]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ (by positivity)) hCg
  set Y : ℝ := ((r : ℝ) + 1) ^ 4 * n ^ 3 with hY
  have hCY : (240 + 2 * |c|) * Y ≤ Cg * Y := mul_le_mul_of_nonneg_right hC (by linarith)
  have hcY : 0 ≤ |c| * Y := mul_nonneg hc (by linarith)
  refine ⟨⟨hk, ?_, by linarith, by linarith⟩, ?_⟩
  · have e1 : 240 * 1 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) :=
      mul_le_mul (by linarith) hge (by norm_num) hCg
    have e2 : 240 * 1 * n ^ 3 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul e1 hZ (by positivity) (by positivity)
    linarith
  · have e0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1) := by positivity
    have e1 : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)) ≤ |c| * (2 * Y) :=
      mul_le_mul (le_abs_self c) h3 e0 hc
    nlinarith

theorem bpNear_gapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam lam0 : Fin n → ℝ) (h : ℝ) (h0 : GapAtLeast ε lam0 h)
    (hg : AllGaps lam0 (200 * l1 lam lam0)) : GapAtLeast ε lam (h / 2) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have h1 := h0 a b hab
  have h2 := hg a b hne
  have hd : ∀ s, |lam s - lam0 s| ≤ l1 lam lam0 := fun s =>
    Finset.single_le_sum (f := fun a => |lam a - lam0 a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have h3 : |lam0 a - lam0 b| ≤ |lam a - lam b| + |lam a - lam0 a| + |lam b - lam0 b| := by
    have e : lam0 a - lam0 b = (lam a - lam b) - (lam a - lam0 a) + (lam b - lam0 b) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith [abs_sub (lam a - lam b) (lam a - lam0 a)])
  linarith [hd a, hd b, abs_nonneg (lam0 a - lam0 b)]

theorem bp_forms_of_thmBpDS : BranchingSupport.Hyps → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.T.exists_local_section_bounds hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.T.standard_bessel_scale_bound
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.capelli_eigen_gap_coef hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
