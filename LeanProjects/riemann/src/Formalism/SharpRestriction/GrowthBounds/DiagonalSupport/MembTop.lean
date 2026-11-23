import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ExistsMapOfCoefGe
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def RestDecG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DecAt p O Fr deg Y N₁ G' cP Dt No Go

def RestAlgG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → AlgAt p O hk Fr Dt rho No Go

def RestDegG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DegAt p O hk Fr d Dt rho No Go

def RestLabG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → LabAt p O Fr Dt rho

theorem membAt_of (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ) (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) :
    MembAt p O hk Fr deg Y N₁ G' cP d := by
  intro J _ Dt dPl dNo ka rho N0 hT hB hNT Gp g1 g2 g4
  obtain ⟨Go, rfl⟩ := exists_map_of_coefGe S Gp g1
  obtain ⟨No, rfl⟩ := exists_map_of_coefGe S N0 hNT.1
  have hMH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go :=
    ⟨hT, hB, hNT, g2, fun mo hmo => g4 mo (by rw [support_of_map]; exact hmo)⟩
  exact membAt_core p O hk Fr deg Y N₁ G' cP d Dt rho No Go
    (hDec p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hAlg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hDeg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hLab p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)

theorem margin_real (r : ℕ) (c s : ℝ) (hr : 2 ≤ r) (hc : 0 ≤ c) (h : 100 * (r : ℝ) ^ 2 * c ≤ s) : 128 * c ≤ s := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have : 400 * c ≤ 100 * (r : ℝ) ^ 2 * c := by nlinarith
  linarith

theorem mfh_of : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
    ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    MFH p F TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) (flatDeg lam0) (dT TT lam0) Y (r + K)
      (cPrime n' r TT.card c0 cpp cStar) := by
  obtain ⟨C0, hC0, H0⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  refine ⟨max C0 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro C hC CLa p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  obtain ⟨_, H, hF, _, _, _⟩ := hD
  have hC0' : C0 ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  have hB := hyps_basic hC1 H
  have hnb := nb_of hC1 H
  have cg0 := counting_hypotheses_of_hyps hC0 (hyps_mono hC0 hC0' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨h1, h2, h3, _, h5, _, _, _, _, h10, h11, _⟩ := H
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  have hfd := fun s hs => flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs
  have hcPe : ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) = Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar := by
    unfold cPrime Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    push_cast
    ring
  rw [hk] at cg0
  have A0 := (H0 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a 0 c0 cpp Dp cStar cg0
    le_rfl (by unfold Formalism.CountingSumsFrames.QII; positivity)).2.1
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  refine ⟨hpF.out, h2, hF, ?_, ?_, ?_⟩
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_pos hs]
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_neg hs]
  · intro jj xx hx hW
    have hBo := Bo_ge hF.2.1 (by omega) p (by omega) (flatDeg lam0) a
      (fun s hs => (hfd s (by rw [hF.1] at hs; exact hs)).1) jj xx hx hW
    have hE : (F.fr jj (r - 1) - F.fr (jj - 1) 0).toNat ≤ goodG' r de h x := by
      have := hF.2.2.1 jj
      omega
    have hq : a / Formalism.CountingSumsFrames.QII p (goodG' r de h x) ≤ Bo p F (flatDeg lam0) jj xx := by
      refine le_trans ?_ hBo
      apply div_le_div_of_nonneg_left ha0 (by positivity)
      exact pow_le_pow_right₀ hp1 hE
    have q := (A0 _ hq).1
    have n1 : 0 ≤ 24 * (((orbitWindowCount r de h x : ℕ) : ℝ) + r) * c0 := by positivity
    have n2 : 0 ≤ Formalism.CountingSumsFrames.mStarII (orbitWindowCount r de h x) (r + K) (Formalism.CountingSumsFrames.QII p (goodG' r de h x))
        (Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar) 0 := by
      unfold Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
      positivity
    have q2 : 100 * (r : ℝ) ^ 2 * ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) ≤
        (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) := by
      rw [hcPe]
      have e : (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) =
          Formalism.CountingSumsFrames.slII Y (r + K) (Bo p F (flatDeg lam0) jj xx) := rfl
      rw [e]
      linarith
    exact margin_real r _ _ h2 (Nat.cast_nonneg _) q2

theorem membership_of_four_parts (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, h1, h2⟩ := mfh_of
  refine ⟨C₁, h1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  exact membAt_of hDec hAlg hDeg hLab p O (dvrOfStd hD.1) hk F TT L₁ L₂ _ _ _ _ Y _
    (h2 C hC CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD)

end Formalism.MainNotions.Proposition5Numerics
