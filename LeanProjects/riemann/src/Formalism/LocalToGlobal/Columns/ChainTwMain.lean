import Formalism.LocalToGlobal.Columns.ChainTwCst

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

open Classical

theorem twIdx_h_g {j : ℕ} {b : (twIdx Ch sel mu cst m2).β j} {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) :
    (twIdx Ch sel mu cst m2).h j b P = 1 :=
  twSt_h_g Ch sel mu cst m2 j b P hP

theorem twIdx_levQ_zero (b : (twIdx Ch sel mu cst m2).β 0) :
    (twIdx Ch sel mu cst m2).levQ 0 b = LevQFam.top X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K)) := rfl

theorem twIdx_levQ_pos {j : ℕ} (hj : j ≠ 0) (b : (twIdx Ch sel mu cst m2).β j) :
    (twIdx Ch sel mu cst m2).levQ j b = twLevQ Ch sel mu cst j ((twSt Ch sel mu cst m2 j).h b) := if_neg hj

theorem twIntAt_pow_inv {P : HeightOneSpectrum (𝓞 X.E)} {z : X.E} {B : ℕ} (hB : 1 ≤ B) (hq : (qOf P : X.E) ≠ 0)
    (hz : IntAt P (((qOf P : X.E) ^ B)⁻¹ * z)) : IntAt P (((qOf P : X.E) ^ 1)⁻¹ * z) := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  have e : ((qOf P : X.E) ^ 1)⁻¹ * z = (qOf P : X.E) ^ B' * (((qOf P : X.E) ^ (B' + 1))⁻¹ * z) := by
    field_simp
    ring
  rw [e]
  refine IntAt.mul ?_ hz
  have e2 : (qOf P : X.E) ^ B' = algebraMap (𝓞 X.E) X.E ((qOf P : 𝓞 X.E) ^ B') := by simp
  rw [e2]
  exact IntAt.coe P _

theorem twSt_chrOk (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) (hC : TwChrQ Ch sel mu cst m2) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → TwDegOne X P.1 → j ≠ 0 →
      TwChrOk Ch sel mu cst j P ((twSt Ch sel mu cst m2 j).h b P)
  | 0, _, _, _, _, h0 => absurd rfl h0
  | i + 1, b, P, hP, hd, _ => by
      by_cases h1 : i + 1 ≤ m2
      · obtain ⟨hb, hnf, ⟨al, hal⟩, hint⟩ := twSt_cand h1 (hN i (by omega)) b P hP
        have hs := twSt_of_twNormAt hN i (by omega) al P hP
        exact hC.1 i (by omega) P hP hd _ _ hs.1 hs.2 hb hnf hint hal
      · revert b
        by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _
          obtain rfl : i = m2 := by omega
          exact hC.2 P hP hd
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

variable (Ch sel mu cst m2) in

theorem twIdx_ok_of (hB : OcbBase Ch sel mu cst m2) (hs : cst.sharp = true) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta)
    (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0) (hwe : cst.WeilTied G.σ₀ G.xi0)
    (hmQ : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K))
    (hmG : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
      G.σ₀ (cst.muq (i + 1) P) = (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K))
    (hA : R.m ≤ cst.A) (hB1 : 1 ≤ cst.B)
    (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (hDQ' : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P)
    (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hF : TwFinQ X Pr R cst.sharp) (hN : TwNormDC Ch sel mu cst m2) (hC : TwChrQ Ch sel mu cst m2) (hZ : TwZeroQ Ch sel mu cst)
    (hAn : TwAnQ Ch sel mu cst m2) :
    (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 := by
  have hm := hB.hm
  have hX := hB.hX
  have hPr := hB.hPr
  have hNall : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i) := twNormAt_all hN hd
  have hψ : ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ a, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) :=
    fun P hP a ha => hB.psi0 P a hP ha
  obtain ⟨hc', hc, -, -, -, -⟩ := ookLast (R := R) hm
  have hΛ := closedLevels_by_entries_holds X Pr R Ch m2 hm
  have hGG := ocbGrpGLoc_holds Ch sel mu cst m2
  have hCG := ocbChrGLoc_holds Ch sel mu cst m2
  have hq0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → (qOf P.1 : X.E) ≠ 0 := fun P hP => by
    exact_mod_cast (ciQOf_prime hPr hP).ne_zero
  let c1 : LocCst X (rowSG Pr sel mu) := { cst with B := 1 }
  have hE1 : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → E1at Ch sel mu cst i P 1 1 = E1at Ch sel mu c1 i P 1 1 :=
    fun i hi P hP => ookE1at_indep Ch sel mu hX hPr c1 hs hm hi P hP (hψ P hP) G.σ₀ hA (le_refl 1) hA hB1
  have hXi : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → XiAt Ch sel mu cst i P 1 1 = XiAt Ch sel mu c1 i P 1 1 :=
    fun i hi P hP => by
      funext y
      show _ * E1at Ch sel mu cst i P 1 1 y = _ * E1at Ch sel mu c1 i P 1 1 y
      rw [hE1 i hi P hP]
  exact
    { hm := hm
      cst_ok := hB.cst_ok
      xiUnitAtPrime := hxi
      weil := hwe
      muqQ := hmQ
      muqG := hmG
      mu0G := fun j => (hT.mu0 j).atg
      psi0 := fun P a hP ha => hB.psi0 P a hP ha
      deep := fun A' B' hA' hB' i hi al be P => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG]
          exact ookE1at_indep Ch sel mu hX hPr cst hs hm hi P hG (hψ P hG) G.σ₀ hA hB1 (le_trans hA hA') (le_trans hB1 hB')
        · exact hAn.deep A' B' hA' hB' i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG)
      zero_uniq := ⟨(), fun _ => rfl⟩
      zero_h := fun _ _ => rfl
      zero_G := fun _ => colLevSym_zero Ch
      zero_Q := fun b => twIdx_levQ_zero b
      last_uniq := by
        show ∃ b : (twSt Ch sel mu cst m2 (m2 + 1)).β, ∀ b', b' = b
        rw [twSt_last]
        exact ⟨(), fun _ => rfl⟩
      last_h := by
        show ∀ (b : (twSt Ch sel mu cst m2 (m2 + 1)).β) P, (twSt Ch sel mu cst m2 (m2 + 1)).h b P = 1
        rw [twSt_last]
        intro _ _
        rfl
      nonvan := fun i hi => by
        have K := fun b P => twNext_nonvan (hNall i hi) b P
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K
      inj := fun i hi b b' H => by
        have K := fun b b' H => twNext_inj (hNall i hi) b b' H
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K b b' H
      surj := fun i hi hh hs' hb H => by
        have hfin : ∀ P, (twCSet Ch sel mu cst (twSt Ch sel mu cst m2 i) P).Finite := fun P =>
          (hF (i + 1) P.1 (Finset.mem_sdiff.1 P.2).2 (hd (twRow P) (Finset.mem_sdiff.1 P.2).2)).subset (fun D ⟨h, hD, hc⟩ => ⟨h, hD, hc.1⟩)
        have K := fun hh hs' hb H => twNext_surj (hNall i hi) hfin (fun al P hP => twSt_h_g Ch sel mu cst m2 i al P hP)
          (fun P hP h hsh H => twSurjG G.σ₀ hB hi P hP h hsh H) (fun P hP => twNonVanG G.σ₀ hB hi P hP) hh hs' hb H
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K hh hs' hb H
      stabG := fun j b P hP => by
        rw [twIdx_h_g hP]
        exact Subgroup.one_mem _
      depthG := hB.depthG
      depthQ := hDQ
      depthQ' := hDQ'
      boundQ := fun j b P hP => twSt_bdd hNall j b P hP
      psiSupp := fun al P x₀ y' h i => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [if_pos hG, pow_one]
          rw [twIdx_h_g hG] at h
          exact (psiAt_sym Ch sel mu cst hc' hc hs P hG x₀ y' h i).1
        · rw [if_neg hG]
          exact hAn.psiSupp P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' h i
      psiInv := fun al P x₀ y' z hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG]
          exact ookPsiInv Ch sel mu hX hPr cst hs hm P hG x₀ y' z fun i => by
            have h1 := hz i
            rwa [if_pos hG, pow_zero, inv_one, one_mul] at h1
        · exact hAn.psiInv P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' z fun i => by
            have h1 := hz i
            rwa [if_neg hG] at h1
      xiSupp := fun i hi al be P x h s l => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG] at h
          exact ookXiSupp Ch sel mu cst hs hm hi P hG x h s l
        · exact hAn.xiSupp i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG) x h s l
      xiInv := fun i hi al be P x z hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG, hXi i hi P hG]
          exact ookXiInv Ch sel mu hX hPr c1 hs hm hi P hG (hψ P hG) G.σ₀ hA rfl x z fun s l =>
            twIntAt_pow_inv hB1 (hq0 P hG) (hz s l)
        · exact hAn.xiInv i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG) x z hz
      psiSuppX := fun al P x₀ y' h s l => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG] at h
          exact ookPsiSuppX Ch sel mu cst hs hm P hG x₀ y' h s l
        · exact hAn.psiSuppX P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' h s l
      psiInvX := fun al P x₀ z y' hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG]
          exact ookPsiInvX Ch sel mu hX hPr c1 hs hm P hG rfl x₀ z y' fun s l => twIntAt_pow_inv hB1 (hq0 P hG) (hz s l)
        · exact hAn.psiInvX P hG _ (twSt_bdd hNall m2 al P hG) x₀ z y' hz
      int := fun j b P => twSt_int hs hNall j b P
      grpQ := fun j b P => by
        have hP : P.1 ∉ Pr.vGs := hQG P.1 P.2
        cases j with
        | zero =>
          rw [twIdx_levQ_zero]
          exact (Subgroup.subgroupOf_eq_top.2 (hZ ⟨P.1, Finset.mem_union_right _ P.2⟩ hP).1).symm
        | succ j' =>
          rw [twIdx_levQ_pos (Nat.succ_ne_zero j')]
          rfl
      chrQ := fun j b P g r hr hx => by
        have hP : P.1 ∉ Pr.vGs := hQG P.1 P.2
        cases j with
        | zero =>
          have e : ((((twIdx Ch sel mu cst m2).levQ 0 b P).lam g : X.Kˣ) : X.K) = 1 := rfl
          rw [e]
          exact ((hZ ⟨P.1, Finset.mem_union_right _ P.2⟩ hP).2 r hr).symm
        | succ j' =>
          have hok := twSt_chrOk hNall hC (j' + 1) b ⟨P.1, Finset.mem_union_right _ P.2⟩ hP (hd _ hP) (Nat.succ_ne_zero j')
          show (((twLam Ch sel mu cst (j' + 1) ⟨P.1, Finset.mem_union_right _ P.2⟩
            ((twSt Ch sel mu cst m2 (j' + 1)).h b ⟨P.1, Finset.mem_union_right _ P.2⟩)) g : X.Kˣ) : X.K) = _
          rw [twLam, dif_pos hok]
          exact twChiVal_eq hok hr hx
      grpG := fun j b w hbar => by
        have hj := twSt_le Ch sel mu cst m2 j b
        rw [twIdx_h_g (P := ⟨w.1, Finset.mem_union_left _ w.2⟩) w.2]
        exact (hΛ.H j hj w hbar).trans (hGG hB j hj w hbar).symm
      chrG := fun j b w hbar g r hr hg hred => by
        have hj := twSt_le Ch sel mu cst m2 j b
        rw [twIdx_h_g (P := ⟨w.1, Finset.mem_union_left _ w.2⟩) w.2] at hr ⊢
        exact (hΛ.lam j hj w hbar).trans (hCG hB j hj w hbar.1 g r hr hg hred).symm }

theorem twIdx_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hK : TwCstQ (Pr := Pr) sel mu G) (hF : TwFinQ X Pr R true) (hN : TwNormDC Ch sel mu (twCst Ch sel mu G) m2)
    (hC : TwChrQ Ch sel mu (twCst Ch sel mu G) m2) (hZ : TwZeroQ Ch sel mu (twCst Ch sel mu G))
    (hAn : TwAnQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have h2 := R.two_le_m
  refine twIdx_ok_of Ch sel mu (twCst Ch sel mu G) m2 (twCst_base hX hPr hCh h4 hK hm) rfl G hT
    (fun P => if hP : P.1 ∈ Pr.vGs then ookXiUnit hCh hW P.1 hP else hK.xi0 P hP) (twCst_weil hX hPr hCh hW hK)
    (fun i h P hP => ?_) (fun i h P hP qu hqu => ?_) (by show R.m ≤ R.m + 1; omega) (by show 1 ≤ R.m + 1; omega)
    (fun P hP => by rw [twCst_D_Q hP]; show 2 * R.m ≤ 2 * R.m; exact le_refl _)
    (fun P hP => by rw [twCst_D_Q hP]; omega) hQG hd hF hN hC hZ hAn
  · show twMuq Ch sel mu G (i + 1) P = _
    unfold twMuq
    rw [if_neg hP, dif_pos (by omega)]
    rfl
  · show G.σ₀ (twMuq Ch sel mu G (i + 1) P) = _
    unfold twMuq
    rw [if_pos hP]
    exact ciMuq_tie G _ hval i h P hP qu hqu

end TwMain

end Formalism.L2.Col
