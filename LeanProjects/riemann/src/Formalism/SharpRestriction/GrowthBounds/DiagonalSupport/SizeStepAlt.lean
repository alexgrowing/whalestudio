import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeCubeMul

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem sizeStep' : ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ [NeZero F.J],
      SizeAt (K := K) p F (fun j : ZMod F.J => (F.LLset (segZ j)).card) (dT TT lam0)
        (CDn * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) ∧
      (∀ (j : ZMod F.J) (u : ℕ), u < (fun j : ZMod F.J => (F.LLset (segZ j)).card) j + r →
        3 / 8 * slU F p (flatDeg lam0) Y (r + K) (fun j : ZMod F.J => (F.LLset (segZ j)).card) j u <
          Bo p F (flatDeg lam0) (segZ j) (posU F ((fun j : ZMod F.J => (F.LLset (segZ j)).card) j) (segZ j) u) / 2) ∧
      1 ≤ cPrime n' r TT.card c0 cpp cStar ∧ 1 ≤ F.J := by
  refine ⟨9, 4, by norm_num, by norm_num, ?_⟩
  intro C hC CLa p W Qq O Kf
  intro _ _ _ _ _ _ _ _ _ _
  intro ι σ j w n' m r
  intro _ _
  intro TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K
  intro _ _
  intro hk F nb B hD _
  have hD' := hD
  unfold DataII at hD'
  obtain ⟨-, hH, hF, -⟩ := hD'
  have hka : ((m + 1 : ℕ) : ℝ) ≤ a := k_le_a (by linarith) hH
  have hH' := hH
  unfold Hyps at hH'
  obtain ⟨hp13, hr2, hOrb, hN, hW, hY, -, hgap, -, -, hcs, hlast⟩ := hH'
  have hF' := hF
  unfold FramesOK at hF'
  obtain ⟨hF1, hV, -, -, -⟩ := hF'
  have hr : 1 ≤ r := by omega
  have hN1 : 1 ≤ orbitWindowCount r de h x := by
    unfold orbitWindowCount
    omega
  have hm : 2 ≤ m := by omega
  have hT : 1 ≤ TT.card := by
    by_contra hc
    have h0 : TT.card = 0 := by omega
    rw [h0, mul_zero] at hN
    have : 1 ≤ orbitWindowCount r de h x ^ 2 := Nat.one_le_pow _ _ hN1
    omega
  have hOrb' := hOrb
  unfold tableLineDegreeFive.OrbitHyp at hOrb'
  obtain ⟨-, -, hLU, -⟩ := hOrb'
  have hU : 1 ≤ goodU de := by omega
  have hG : goodG' r de h x ≠ 0 := by
    unfold goodG' goodEll
    exact Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega))
  have hA1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 m)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hT1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hT
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hpl : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hQ1 : (1 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := one_le_pow₀ (one_le_pow₀ hp1)
  have hpQ : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 :=
    le_trans (le_self_pow₀ hp1 hG) (le_self_pow₀ (one_le_pow₀ hp1) (by norm_num))
  have hc1 : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
  have hS : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ)) := by
    have : (0 : ℝ) ≤ (r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ) := by positivity
    linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hA3 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hA1
  have hCT : C * (TT.card : ℝ) ≤ a := by
    have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA3 hr1) hQ1) hS) hY1
    have h0 : (0 : ℝ) ≤ C * (TT.card : ℝ) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc C * (TT.card : ℝ) = C * (TT.card : ℝ) * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hQa : ((p : ℝ) ^ goodG' r de h x) ^ 5 ≤ a := by
    have h1 : (1 : ℝ) ≤ C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hC1 hA3) hr1) hT1) hS) hY1
    have h0 : (0 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc ((p : ℝ) ^ goodG' r de h x) ^ 5 = ((p : ℝ) ^ goodG' r de h x) ^ 5 * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hpa : (p : ℝ) ≤ a := le_trans hpQ hQa
  have h7 : (7 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 7 ≤ m + 1)
  have hlog : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hpl]
    exact Real.logb_le_logb_of_le hpl (by linarith) hpa
  have hnb : NB p m r TT.card a := by
    refine ⟨by linarith, hpa, ?_, ?_, hlog, ?_⟩
    · have : 4 * (TT.card : ℝ) ≤ C * (TT.card : ℝ) := mul_le_mul_of_nonneg_right hC (by positivity)
      linarith
    · have : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
      linarith
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hA1)) hlog
  have hW' := hW
  unfold tableLineDegreeFive.WeightHyp at hW'
  obtain ⟨hBW, -, hab⟩ := hW'
  have hv : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  have hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a := by
    intro s hs
    obtain ⟨h0, -, hmid⟩ := (hBW s).1 hs
    have hl := hmid 1 (by omega) (by omega)
    have hl' : |((lam0 s 1 : ℤ) : ℝ)| ≤ (cpp : ℝ) := by exact_mod_cast hl
    obtain ⟨hl1, hl2⟩ := abs_le.mp hl'
    obtain ⟨haT1, haT2, -, -⟩ := hab s hs
    have hv0R : (0 : ℝ) ≤ ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by linarith
    have hv0 : 0 ≤ aT s - lam0 s 1 := by exact_mod_cast hv0R
    have e : ((flatDeg lam0 s : ℕ) : ℝ) = ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by
      unfold flatDeg
      rw [h0, ← Int.cast_natCast, Int.toNat_of_nonneg hv0, Int.cast_sub]
    rw [e]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sizeAt_of (K := K) hk hF hr hnb hka hfd (fun j : ZMod F.J => (F.LLset (segZ j)).card) rfl (fun _ => rfl)
  · intro j u hu
    exact sl_lt_Bo hV hr p (by omega) (flatDeg lam0) a (by linarith)
      (fun s hs => (hfd s (by rw [hF1] at hs; exact hs)).1) Y (r + K) (by linarith) (by omega)
      (fun j : ZMod F.J => (F.LLset (segZ j)).card) (fun _ => rfl) j u hu
  · unfold cPrime
    omega
  · have hV' := hV
    unfold Frames.Valid at hV'
    exact hV'.1

end Formalism.MainNotions.Proposition5Numerics
