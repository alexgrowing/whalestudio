import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.HermitianCurvature.StatementTBB
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselEnergyNormalisedFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVectorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatioStatement
import Formalism.FormalDegreeBessel.FinalG
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.BasicNotions

namespace GlobalTheory.ThA.BpDict

theorem ptEntry_swap (bs : List (ℂ × ℕ)) : ∀ a b : ℕ,
    D.ptEntry (bs.map fun b => (b.2, b.1)) a b = ptEntry bs a b := by
  induction bs with
  | nil => intro a b; rfl
  | cons x bs ih =>
    intro a b
    obtain ⟨t, s⟩ := x
    rw [List.map_cons, D.ptEntry.eq_def, ptEntry.eq_def]
    simp only [ih]

theorem isLocPt_swap {i : ℕ} (γ : Point ℂ i) : D.IsLocPt (γ.1.map fun b => (b.2, b.1)) i := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact ⟨(γ.2.1 c hc).2, (γ.2.1 c hc).1⟩
  · unfold D.ptSize
    rw [List.map_map]
    exact γ.2.2

theorem ptG_swap {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    D.ptG (T * T') r (γ.1.map fun b => (b.2, b.1)) = ThB.Gpt T T' γ := by
  have h : ∀ (l : ℕ) (hl : l ≤ r + 1), D.ptMatN (γ.1.map fun b => (b.2, b.1)) l =
      (ptMat γ).submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    intro l hl
    ext a b
    exact ptEntry_swap γ.1 a b
  unfold D.ptG ThB.Gpt leadMinor
  rw [h (r + 1) le_rfl, h r (Nat.le_succ r)]

theorem weightFrom_swap (k r : ℕ) (hk : 1 ≤ k) (T T' GG : ℝ) (bs : List (ℂ × ℕ)) : ∀ x : ℕ,
    (∀ b ∈ bs, 1 ≤ b.2) → x + (bs.map Prod.snd).sum = r + 1 →
    (∀ b, bs.getLast? = some b → GG = Complex.normSq b.1 - T * T') →
    ptWeightFrom k r T T' x bs = C.nAux k r GG (fun _ _ => 1) (x + 1) (bs.map fun b => (b.2, b.1)) := by
  induction bs with
  | nil => intro x _ _ _; rfl
  | cons y bs ih =>
    intro x h1 h2 h3
    obtain ⟨t, s⟩ := y
    have hs : 1 ≤ s := h1 (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at h2
    rw [List.map_cons, ptWeightFrom.eq_2, C.nAux.eq_2]
    have hrec : ptWeightFrom k r T T' (x + s) bs =
        C.nAux k r GG (fun _ _ => 1) (x + 1 + s) (bs.map fun b => (b.2, b.1)) := by
      rw [show x + 1 + s = x + s + 1 by omega]
      refine ih (x + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb)) (by omega) ?_
      intro b hb
      apply h3
      cases bs with
      | nil => simp at hb
      | cons z bs => rw [List.getLast?_cons_cons]; exact hb
    rw [hrec]
    congr 1
    by_cases hc : s = 1 ∧ x + 1 = r + 1
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩]
      have hnil : bs = [] := by
        cases bs with
        | nil => rfl
        | cons z bs =>
          exfalso
          have := h1 z (by simp)
          simp only [List.map_cons, List.sum_cons] at h2
          omega
      subst hnil
      rw [h3 (t, s) rfl]
    · rw [if_neg hc, if_neg (by omega), one_mul, ← zpow_natCast]
      congr 1
      unfold Ml C.Mlev
      have e1 : x + 1 + s - 1 = x + s := by omega
      rw [e1]
      have e2 : x + s ≤ r + 1 := by omega
      have e3 : 3 ≤ 2 * (r + 1 - (x + s)) + k + 1 + s := by omega
      push_cast [Nat.cast_sub e2, Nat.cast_sub e3]
      ring

theorem ptWeight_swap (k r : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r T T' γ = TBB.nPt k r (T * T') (γ.1.map fun b => (b.2, b.1)) := by
  unfold ptWeight TBB.nPt
  refine weightFrom_swap k r hk T T' _ γ.1 0 (fun b hb => (γ.2.1 b hb).2) (by rw [zero_add]; exact γ.2.2) ?_
  intro b hb
  unfold D.ptGG D.ptLast
  rw [List.getLast?_map, hb]
  rfl

theorem aT_one (k r : ℕ) : aT k r 1 = 1 := by
  unfold aT
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp

theorem conjF_one {k r : ℕ} {V : Type*} (F : B.Mat k r → V) : conjF 1 F = F := by
  funext x
  unfold conjF
  rw [aT_one]; simp

theorem gamLev_one (k r : ℕ) : D.GamLev k r 1 1 0 = 1 := by
  unfold D.GamLev
  simp

theorem const_le (r c n : ℕ) (b C₄ Cb G : ℝ) (hc : c ≤ (r + 1) ^ 2) (hb : 3 ≤ b) (hC : C₄ + 1 ≤ Cb)
    (hn : (n : ℝ) ≤ Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) (hG : 0 < G) :
    (Real.pi ^ c) ^ 2 * (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n) ≤
      b ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * (max 1 (1 / G)) ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) := by
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : (Real.pi ^ c) ^ 2 ≤ b ^ (((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
    have hpi : Real.pi ≤ b ^ 2 := by nlinarith [Real.pi_le_four]
    calc (Real.pi ^ c) ^ 2 ≤ ((b ^ 2) ^ c) ^ 2 := by gcongr
      _ = b ^ (4 * c) := by ring
      _ ≤ b ^ ((2 * r + 2) ^ 4) := by
        refine pow_le_pow_right₀ hb1 ?_
        have : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        have e : (2 * r + 2) ^ 4 = 16 * (r + 1) ^ 4 := by ring
        omega
      _ = _ := by rw [← Real.rpow_natCast]; push_cast; rfl
  have h2 : G⁻¹ ^ n ≤ (max 1 (1 / G)) ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) := by
    calc G⁻¹ ^ n ≤ (max 1 (1 / G)) ^ n := by
          refine pow_le_pow_left₀ (by positivity) ?_ n
          rw [one_div]; exact le_max_right _ _
      _ = (max 1 (1 / G)) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hn
  rw [← mul_assoc]
  refine mul_le_mul ?_ h2 (by positivity) (by positivity)
  calc (Real.pi ^ c) ^ 2 * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4)
      ≤ b ^ (((2 * r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by gcongr
    _ = b ^ ((C₄ + 1) * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by rw [← Real.rpow_add hb0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr)

theorem hsNormSq_nonneg {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => inner_self_nonneg (𝕜 := ℂ)

theorem orbSq_eq_zero {k r : ℕ} (L : LocBessel k r) (F : ThB.Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (hG : ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ < 0) : ThB.orbSq L F γ = 0 := by
  unfold ThB.orbSq
  simp only [ENNReal.iSup_eq_zero]
  intro g _ _ h
  exfalso
  have h0 := gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g h.1.1
  unfold Gf Dmin at h0
  rw [h.1.2] at h0
  exact absurd hG (not_lt.2 h0)

theorem card_rootPat_le {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ).card ≤ (r + 1) ^ 2 := by
  refine (Finset.card_le_univ _).trans ?_
  simp [sq]

theorem bpIneq_of_thmBpAt : ∃ c₃ : ℝ, ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (A b C₄ Cb : ℝ) (n₀ p₀ : ℕ), IsStdOf L μsec p.T.base → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → c₃ * ((D.R.rS : ℝ) + 1) ^ 2 * ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 f → 3 ≤ b → C₄ + 1 ≤ Cb → ((2 * p₀ + n₀ : ℕ) : ℝ) ≤ Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 → TBB.ThmBpAt p f b C₄ n₀ p₀ → ∀ γ : Point ℂ (D.R.rS + 1), ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → ThB.BpIneq D Cb L f μsec b γ := by
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.T.orbitalSquare_eq_hilbertSchmidt_normalisedVector
  refine ⟨c₃, ?_⟩
  intro D L μsec U U' p f A b C₄ Cb n₀ p₀ hstd hc hκ0 hκt hA hf hb hC hn hBp γ hγ
  unfold ThB.BpIneq
  rcases lt_or_gt_of_ne hγ with hG | hG
  · rw [orbSq_eq_zero L f γ hG, mul_zero]; exact zero_le
  obtain ⟨cN, hcN⟩ := GlobalTheory.T.exists_unipotentHaarMeasure_ratio D.R.k D.R.rS
  have hk : 1 ≤ D.R.k := p.T.base.k_pos
  have hc0 : (cStd : ℂ) ≠ 0 := by unfold cStd; simp
  have hcc : cStd / L.c = 1 := by rw [hc]; exact div_self hc0
  have horb := hc₃ D.R.k D.R.rS L μsec p.T.base cN A p.ν' p.m₀ f hstd hcN hc hκ0 hκt p.hF hA hf γ hG
  have hnorm := GlobalTheory.T.besselEnergy_normalised_frame_change D.R.k D.R.rS L μsec p.T.base cN f hk hstd hcN (hc ▸ hc0) hκ0 hκt
  have hj : ThB.jNorm2 L f μsec = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4) * TBB.jN2 p f := by
    rw [GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq]
    unfold lamN at hnorm
    rw [hcc, conjF_one, norm_one, inv_one, gamLev_one, one_pow, mul_one, div_one] at hnorm
    refine Eq.trans ?_ hnorm
    unfold ThB.jNorm2 jNormSq
    refine lintegral_congr fun q => ?_
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hsNormSq_nonneg _)]
  have hTT : TBB.TTp p = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold TBB.TTp
    rw [hstd.1, hstd.2.1]
  have hGp : TBB.Gp p (γ.1.map fun b => (b.2, b.1)) = ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold TBB.Gp
    rw [hTT]
    exact ptG_swap _ _ γ
  have hB := hBp _ (isLocPt_swap γ) (hGp ▸ hG)
  rw [P.TBBx2.Tri.Ew_top p f (isLocPt_swap γ), hGp, hTT] at hB
  rw [horb, hj, ptWeight_swap _ _ hk]
  have hle := const_le D.R.rS (rootPat γ).card (2 * p₀ + n₀) b C₄ Cb _ (card_rootPat_le γ) hb hC hn hG
  unfold KB.Pl.V at hB
  dsimp only at hB
  set n := TBB.nPt D.R.k D.R.rS (Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z') (γ.1.map fun b => (b.2, b.1)) with hn'
  rcases le_total n 0 with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0, zero_mul]; exact zero_le
  rw [Real.mul_self_sqrt h0] at hB
  set v := ‖B.hsVec (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ f (γ.1.map fun b => (b.2, b.1)))‖ ^ 2 with hv
  set K := (L.κN.toReal * cN) ^ 4 with hK
  set Q := (Real.pi ^ (rootPat γ).card) ^ 2 with hQ
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have e1 : ENNReal.ofReal n * ENNReal.ofReal (K * Q * v) =
      ENNReal.ofReal K * (ENNReal.ofReal Q * ENNReal.ofReal (n * v)) := by
    rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul hQ0, ← ENNReal.ofReal_mul hK0]
    congr 1; ring
  rw [e1, mul_left_comm _ (ENNReal.ofReal K)]
  refine mul_le_mul_right ?_ _
  refine (mul_le_mul_right hB _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hQ0]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hle) _

end GlobalTheory.ThA.BpDict
