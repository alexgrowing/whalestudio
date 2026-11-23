import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffMonomial

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Var

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (hk : m + 1 = r + K) {J : ℕ} (nL : ZMod J → ℕ)

theorem var_cases (x0 : TL J nL r) (b : Fin (m + 1)) :
    (∃ a : Fin r, (posOf n' (posTL Fr x0), b) = plVar Fr hk nL x0 a) ∨
      ∃ c : Fin K, (posOf n' (posTL Fr x0), b) = noVar Fr hk nL x0 c := by
  by_cases hb : b.val < r
  · left
    refine ⟨⟨b.val, hb⟩, ?_⟩
    unfold Formalism.MainNotions.TestSideWords.plVar
    exact Prod.ext rfl (Fin.ext rfl)
  · right
    have h1 := b.isLt
    refine ⟨⟨b.val - r, by omega⟩, ?_⟩
    unfold Formalism.MainNotions.TestSideWords.noVar
    refine Prod.ext rfl (Fin.ext ?_)
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega

end Var

section Main

variable (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] (hk : m + 1 = r + K) (Fr : Frames n' r)
  (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

include D in

theorem derLev (hTP : TrDerPl) (hTN : TrDerNo) (hPD : PlDer) (hPE : PlEul) (hNO : NoOpStep) {n'' : ℕ}
    (S : UniformizedDVR p O) (hR : AdmissibleDVR p n'' O) (hB : Base Fr p Dt) (x0 : TL J Dt.nL r)
    (hu : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) (hG : TouchAt Fr Dt x0)
    (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (F : MvPolynomial (TV n' (m + 1)) (KK O))
    (hF : MemLev sc sL loss p O hk Fr deg Y N₁ G' cP Dt F) (b : Fin (m + 1)) :
    MemLev sc sL (fun jz u => loss jz u + cost1 Fr (posOf n' (posTL Fr x0)) jz u) p O hk Fr deg Y N₁ G' cP Dt
      (pderiv (posOf n' (posTL Fr x0), b) F) := by
  intro dPl dNo ka th thL hpos hT rho e he nu
  have hDrop := thDrop_of hB hG th thL
  rcases var_cases Fr hk Dt.nL x0 b with ⟨a, hv⟩ | ⟨c, hv⟩
  · obtain ⟨c1, c2, c3, rho1, rho2, hEq⟩ := hTP p O hk Fr Dt.nL x0 hu a rho dPl dNo F
    rw [hv, hEq]
    simp only [oneT_add, oneT_smul, planeCoeff_add, planeCoeff_smul, oneT_X_mul, oneT_pderiv, planeCoeff_X_mul,
      planeCoeff_pderiv]
    refine XXg_add Dt (XXg_add Dt (XXg_smul Dt c1 ?_) (XXg_smul Dt c2 ?_)) (XXg_smul Dt c3 ?_)
    · exact hF dPl dNo ka th thL hpos (thLe_weak hT) rho1 e he nu
    · exact hPE p O Dt x0 a dPl th _ thL _ hDrop _
        (hF dPl dNo ka _ _ (thLUp_pos hpos) (thLe_up hT) rho1 e he nu)
    · exact hPD p O Dt x0 a dPl th _ thL _ hDrop _
        (hF _ dNo ka _ _ (thLUp_pos hpos) (thLe_up hT) rho2 e he nu)
  · obtain ⟨c1, c2, c3, rho1, rho2, hEq⟩ := hTN p O hk Fr Dt.nL x0 hu c rho dPl dNo F
    rw [hv, hEq]
    simp only [oneT_add, oneT_smul, planeCoeff_add, planeCoeff_smul, oneT_oneT]
    refine XXg_add Dt (XXg_add Dt (XXg_smul Dt c1 ?_) (XXg_smul Dt c2 ?_)) (XXg_smul Dt c3 ?_)
    · exact hF dPl dNo ka th thL hpos (thLe_weak hT) rho1 e he nu
    · exact hNO D p O K S hR Dt x0 c _ (Or.inr (Or.inr rfl)) dPl th thL _ ka e he
        (fun ka1 hka e1 he1 nu1 => hF dPl dNo ka1 th thL hpos (thLe_ka hB hG hT hka) rho1 e1 he1 nu1) nu
    · exact hNO D p O K S hR Dt x0 c _ (Or.inl rfl) dPl th thL _ ka e he
        (fun ka1 hka e1 he1 nu1 => hF dPl _ ka1 th thL hpos (thLe_ka hB hG hT hka) rho2 e1 he1 nu1) nu

include D in

theorem mulLev (hTP : TrMulPl) (hTN : TrMulNo) (hPM : PlMul) (hNO : NoOpStep) {n'' : ℕ}
    (S : UniformizedDVR p O) (hR : AdmissibleDVR p n'' O) (hB : Base Fr p Dt) (x0 : TL J Dt.nL r)
    (hu : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) (hG : TouchAt Fr Dt x0)
    (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (F : MvPolynomial (TV n' (m + 1)) (KK O))
    (hF : MemLev sc sL loss p O hk Fr deg Y N₁ G' cP Dt F) (b : Fin (m + 1)) :
    MemLev sc sL (fun jz u => loss jz u + cost1 Fr (posOf n' (posTL Fr x0)) jz u) p O hk Fr deg Y N₁ G' cP Dt
      (X (posOf n' (posTL Fr x0), b) * F) := by
  intro dPl dNo ka th thL hpos hT rho e he nu
  have hDrop := thDrop_of hB hG th thL
  rcases var_cases Fr hk Dt.nL x0 b with ⟨a, hv⟩ | ⟨c, hv⟩
  · obtain ⟨c1, c2, rho1, rho2, h0, hEq⟩ := hTP p O hk Fr Dt.nL x0 hu a rho dPl dNo F
    rw [hv, hEq]
    simp only [oneT_add, oneT_smul, planeCoeff_add, planeCoeff_smul, oneT_X_mul, planeCoeff_X_mul]
    refine XXg_add Dt (XXg_smul Dt c1 ?_) ?_
    · exact hF dPl dNo ka th thL hpos (thLe_weak hT) rho1 e he nu
    · by_cases hd : dPl x0 = 0
      · rw [h0 hd, zero_smul]
        exact XXg_zero Dt
      · exact XXg_smul Dt c2 (hPM p O Dt x0 a dPl th _ thL _ hDrop (Nat.one_le_iff_ne_zero.2 hd) _
          (hF _ dNo ka _ _ (thLUp_pos hpos) (thLe_up hT) rho2 e he nu))
  · obtain ⟨c1, c2, rho1, rho2, hEq⟩ := hTN p O hk Fr Dt.nL x0 hu c rho dPl dNo F
    rw [hv, hEq]
    simp only [oneT_add, oneT_smul, planeCoeff_add, planeCoeff_smul, oneT_oneT]
    refine XXg_add Dt (XXg_smul Dt c1 ?_) (XXg_smul Dt c2 ?_)
    · exact hF dPl dNo ka th thL hpos (thLe_weak hT) rho1 e he nu
    · exact hNO D p O K S hR Dt x0 c _ (Or.inr (Or.inl rfl)) dPl th thL _ ka e he
        (fun ka1 hka e1 he1 nu1 => hF dPl _ ka1 th thL hpos (thLe_ka hB hG hT hka) rho2 e1 he1 nu1) nu

end Main

def OpSteps : Prop :=
  TrDerPl ∧ TrDerNo ∧ TrMulPl ∧ TrMulNo ∧ PlDer ∧ PlEul ∧ PlMul ∧ NoOpStep ∧ GeoTop ∧ GeoTouch

theorem oneOpStep_of (D : Formalism.BasicNotions.D7) (h : OpSteps) (C CLa : ℝ) : OneOpStep C CLa := by
  obtain ⟨hDP, hDN, hMP, hMN, hPD, hPE, hPM, hNO, hGT, hGU⟩ := h
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD loss Fp hFp s hs a' b'
  have hSet := hD.1
  have hG1 : AdmissibleDVR p n' O := Formalism.MainNotions.flipOneThree.admissible_dvr_of_unramified_quadratic_setting hSet
  have hK : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero (dvrOfStd hSet) hG1.prime
  have hFO := hD.2.2.1
  have hV := hFO.2.1
  have hs' : s ∈ F.TT := by rw [hFO.1]; exact hs
  rw [memAtLe_iff] at hFp ⊢
  intro J _ Dt hB
  obtain ⟨x0, hx0, huq⟩ := hGT F L₁ _ hV Dt.nL hB.1 hB.2.1 s hs'
  subst hx0
  have hG : TouchAt F Dt x0 := hGU F L₁ _ hV Dt.nL hB.1 hB.2.1 x0
  have h1 := derLev D p O hk F (flatDeg lam0) Y _ _ _ Dt hDP hDN hPD hPE hNO (dvrOfStd hSet) hG1 hB x0 huq hG 0 (1 / 8)
    loss Fp (hFp J Dt hB) b'
  have h2 := mulLev D p O hk F (flatDeg lam0) Y _ _ _ Dt hMP hMN hPM hNO (dvrOfStd hSet) hG1 hB x0 huq hG 0 (1 / 8)
    _ _ h1 a'
  have e : (fun jz u => loss jz u + opCost F (posOf n' (posTL F x0)) jz u) =
      fun jz u => loss jz u + cost1 F (posOf n' (posTL F x0)) jz u + cost1 F (posOf n' (posTL F x0)) jz u := by
    funext jz u
    rw [opCost_eq]
    ring
  rw [e]
  exact h2

theorem restOneOp_of (h : OpSteps) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestOneOp D CLa Ck Crk Cdeg :=
  fun _ => ⟨1, one_pos, fun C _ => oneOpStep_of D h C CLa⟩

end Formalism.MainNotions.PairMembershipBlocks
