import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PreChainLe

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem vb_arith1 (T s c : ℝ) (hc : 0 ≤ c) : T - s / 2 - 60 * c ≤ T - s / 8 - 3 / 8 * s - 24 * c := by linarith

theorem vb_arith2 (T s c : ℝ) (hs : 0 ≤ s) : T - s / 2 - 60 * c ≤ T - 3 / 8 * s - 60 * c := by linarith

theorem multideg_mapDomain {ι κ : Type} [Fintype ι] {n : ℕ} (g : ι → κ) (u : ι × Fin n →₀ ℕ) (i : κ) :
    multideg (Finsupp.mapDomain (fun v : ι × Fin n => (g v.1, v.2)) u) i =
      ∑ x : ι, if g x = i then multideg u x else 0 := by
  unfold multideg
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h₁, h₂]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  | single a b =>
    rw [Finsupp.mapDomain_single]
    obtain ⟨a1, a2⟩ := a
    by_cases h : g a1 = i
    · subst h
      simp [Finsupp.single_apply]
      rw [Finset.sum_eq_single a1]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · simp [Finsupp.single_apply, h]
      symm
      apply Finset.sum_eq_zero
      intro x _
      split_ifs with hx
      · have hne : a1 ≠ x := fun e => h (e ▸ hx)
        simp [hne]
      · rfl

section L

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} {nL : ZMod J → ℕ}

theorem ml_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (y : ML J nL r) :
    (mlPos Fr nL y).2 ∈ Fr.letters (segZ (mlPos Fr nL y).1) := by
  have hv := hV
  obtain ⟨-, -, hinc, hstep, hTT, -⟩ := hv
  have hmon : ∀ k : ℤ, ∀ a b : ℕ, a ≤ b → b < r → Fr.fr k a ≤ Fr.fr k b := by
    intro k a b hab hb
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this
      exact le_rfl
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact (ih (by omega) (by omega)).trans (hinc k b hb).le
  cases y with
  | ll j l =>
    simp only [mlPos]
    apply (LL_sub_letters hV hr _ _ _).1
    have hl : (l : ℕ) < ((Fr.LLset (segZ j)).sort (· ≤ ·)).length := by
      rw [Finset.length_sort, ← hnL]
      exact l.2
    unfold llPos
    rw [List.getD_eq_getElem _ _ hl]
    exact (Finset.mem_sort _).mp (List.getElem_mem hl)
  | lab j m =>
    simp only [mlPos]
    exact fr_mem_letters hV hr _ _ (by omega)
  | wc j m =>
    simp only [mlPos]
    rw [dv_mem_letters]
    have h1 := hstep (segZ (j + 1) - 1)
    rw [sub_add_cancel] at h1
    refine ⟨⟨hmon _ _ _ (by omega) (by omega), ?_⟩, (hTT _ _ (by omega)).1⟩
    exact ((hmon _ _ _ (by omega) (by omega)).trans h1.le).trans (hmon _ _ _ (by omega) (by omega))
  | tp j m h =>
    simp only [mlPos]
    exact fr_mem_letters hV hr _ _ (by omega)

theorem tl_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (x : TL J nL r) :
    (tlPos Fr nL x).2 ∈ Fr.letters (segZ (tlPos Fr nL x).1) ∧ ¬ Fr.IsW (segZ (tlPos Fr nL x).1) (tlPos Fr nL x).2 := by
  have hv := hV
  obtain ⟨-, -, hinc, hstep, -⟩ := hv
  have hmon : ∀ k : ℤ, ∀ a b : ℕ, a ≤ b → b < r → Fr.fr k a ≤ Fr.fr k b := by
    intro k a b hab hb
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this
      exact le_rfl
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact (ih (by omega) (by omega)).trans (hinc k b hb).le
  obtain ⟨j, l | m⟩ := x
  · simp only [tlPos, posTL]
    apply LL_sub_letters hV hr
    have hl : (l : ℕ) < ((Fr.LLset (segZ j)).sort (· ≤ ·)).length := by
      rw [Finset.length_sort, ← hnL]
      exact l.2
    unfold llPos
    rw [List.getD_eq_getElem _ _ hl]
    exact (Finset.mem_sort _).mp (List.getElem_mem hl)
  · simp only [tlPos, posTL]
    refine ⟨fr_mem_letters hV hr _ _ (by omega), ?_⟩
    unfold Frames.IsW
    have h1 := hstep (segZ j - 1)
    rw [sub_add_cancel] at h1
    exact not_le.mpr (h1.trans_le (hmon _ _ _ (by omega) (by omega)))

end L

section Main

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ)
  (cP : ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
  (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
  (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

theorem valBd_of (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP)
    (hH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go) : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go := by
  have hF := hM.frames
  have hV : Fr.Valid L₁ N₁ := hF.2.1
  have hr : 1 ≤ r := by
    have := hM.two_le_r
    omega
  unfold MH SignedChainDegreeCondition Tied NormTest at hH
  obtain ⟨⟨⟨hJ, hnL, hsgn, -, -, hnch, hchain, hth, hthL⟩, hc, hsl⟩, -, ⟨-, -, hNorm⟩, hY, -⟩ := hH
  obtain ⟨hYc, hYl⟩ := hY
  have hc0 : (0 : ℝ) ≤ (cP : ℝ) := Nat.cast_nonneg _
  unfold ValBd
  refine ⟨?_, ?_, ?_⟩
  · intro j u hu
    unfold pU
    by_cases hul : u ≤ Dt.nL j
    · have hi : u < Dt.nch j := by
        rw [hnch]
        omega
      have hpre := pre_chain Dt hV hr hnL hchain j ⟨u, hi⟩ hul
      apply val_of_pre Dt hV hsgn Go _ _ hpre
      refine geZ_le ?_ (hYc j ⟨u, hi⟩)
      rw [hth, hsl, hc]
      unfold tauU
      exact vb_arith1 _ _ _ hc0
    · have hm : r - 1 - (u - Dt.nL j) < r := by omega
      have hmm2 : r - 1 - (u - Dt.nL j) + 2 ≤ r := by omega
      have hu' : Dt.nL j + (r - 1 - (r - 1 - (u - Dt.nL j))) = u := by omega
      have hpre := pre_link Dt hV hr hnL j ⟨r - 1 - (u - Dt.nL j), hm⟩ hmm2
      simp only [hu'] at hpre
      apply val_of_pre Dt hV hsgn Go _ _ hpre
      have h1 := hYl j ⟨r - 1 - (u - Dt.nL j), hm⟩ hmm2
      have h2 := Formalism.MainNotions.G.Joints.valS_le_union Dt.modelLet (Dt.linkML j ⟨r - 1 - (u - Dt.nL j), hm⟩)
        {y : ML J Dt.nL r | ∃ m' : Fin r, (⟨r - 1 - (u - Dt.nL j), hm⟩ : Fin r) < m' ∧ y = ML.lab j m'}
        (by
          rintro _ ⟨m', -, rfl⟩
          rfl)
        (MvPolynomial.map (algebraMap O (KK O)) Go)
      have hs : (0 : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j u := by
        have hx := tl_mem_letters hV hr hnL (⟨j, Sum.inr ⟨r - 1 - (u - Dt.nL j), hm⟩⟩ : TL J Dt.nL r)
        have hmg := hM.margin _ _ hx.1 hx.2
        have hpos : (tlPos Fr Dt.nL (⟨j, Sum.inr ⟨r - 1 - (u - Dt.nL j), hm⟩⟩ : TL J Dt.nL r)) =
            (j, posU Fr (Dt.nL j) (segZ j) u) := by
          simp only [tlPos, posTL, posU, if_neg (show ¬ u < Dt.nL j by omega)]
          congr 2
          omega
        rw [hpos] at hmg
        unfold slU
        have hcp : (0 : ℝ) ≤ 128 * (cP : ℝ) := by positivity
        have hmg' : (128 * (cP : ℝ)) ≤ ((sl p Fr deg Y (r + K) (segZ j) (posU Fr (Dt.nL j) (segZ j) u) : ℤ) : ℝ) := by
          exact_mod_cast hmg
        linarith
      intro k hk
      rw [hk] at h2
      obtain ⟨k', hk'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h2)
      rw [← hk'] at h2
      have h3 := h1 k' hk'.symm
      have h4 : k' ≤ k := WithTop.coe_le_coe.mp h2
      rw [hthL j _ hmm2, hc] at h3
      simp only [hu'] at h3
      unfold tauU
      have h5 := vb_arith2 (thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u)
        (slU Fr p deg Y (r + K) Dt.nL j u) (cP : ℝ) hs
      have h6 : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast h4
      linarith
  · intro j u hu
    unfold pU
    have hi : u + 1 < Dt.nch j := by
      rw [hnch]
      omega
    have hpre := pre_chain_le Dt hV hr hnL hchain j ⟨u + 1, hi⟩ u rfl hu
    apply val_of_pre Dt hV hsgn Go _ _ hpre
    refine geZ_le ?_ (hYc j ⟨u + 1, hi⟩)
    rw [hth, hsl, hc]
    unfold tauU
    exact vb_arith1 _ _ _ hc0
  · intro j u hu
    unfold pU
    exact ⟨lam_of_pre Dt hV hsgn No _ _ (tl_pre_lt hV hnL j u hu) _ (hNorm j u hu.le),
      lam_of_pre Dt hV hsgn No _ _ (tl_pre_le hV hnL j u hu) _ (hNorm j (u + 1) hu)⟩

theorem suppOK_of (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP)
    (hH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go) : SuppOK p O Fr Dt dNo No Go := by
  unfold MH SignedChainDegreeCondition Tied NormTest at hH
  obtain ⟨⟨⟨hJ, hnL, -⟩, -⟩, -, ⟨-, hPol, -⟩, -⟩ := hH
  have hF := hM.frames
  unfold FramesOK at hF
  have hV : Fr.Valid L₁ N₁ := hF.2.1
  have hr : 1 ≤ r := by
    have := hM.two_le_r
    omega
  unfold SuppOK
  refine ⟨?_, ?_⟩
  · intro mo hmo v hv
    unfold xiPl at hmo
    obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ (MvPolynomial.mem_support_iff.mp hmo)
    have hv' := Finsupp.mapDomain_support hv
    rw [Finset.mem_image] at hv'
    obtain ⟨w, -, rfl⟩ := hv'
    exact ml_mem_letters hV hr hnL w.1
  · intro mo hmo
    unfold xiNo at hmo
    obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ (MvPolynomial.mem_support_iff.mp hmo)
    refine ⟨?_, ?_⟩
    · intro v hv
      have hv' := Finsupp.mapDomain_support hv
      rw [Finset.mem_image] at hv'
      obtain ⟨w, -, rfl⟩ := hv'
      exact tl_mem_letters hV hr hnL w.1
    · intro i
      rw [multideg_mapDomain (tlPos Fr Dt.nL) u i]
      unfold dNoOf
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · have hu' : u ∈ ((MvPolynomial.map (algebraMap O (KK O))) No).support := by
          rw [support_of_map]
          exact MvPolynomial.mem_support_iff.mpr hu
        unfold Pol at hPol
        rw [MvPolynomial.mem_restrictSupport_iff] at hPol
        exact hPol hu' x
      · rfl

end Main

theorem restValBdG : RestValBdG := by
  intro p _ n' r K _ _ _ O _ _ _ _ Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hH
  exact ⟨valBd_of p O Fr TT L₁ L₂ N₁ G' deg d Y cP Dt dPl dNo ka rho No Go hM hH,
    suppOK_of p O Fr TT L₁ L₂ N₁ G' deg d Y cP Dt dPl dNo ka rho No Go hM hH⟩

end Formalism.MainNotions.Proposition5Numerics
