import Formalism.HermitianCurvature.StatementM

namespace Formalism.FourierDecayAlt.P

open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M

namespace Mx9

theorem eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

theorem star_eq {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h

theorem far {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith

noncomputable def ty0 (P : Par) : Ty P := fun _ => 0

theorem xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h

theorem qC_ne (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h

theorem ypt_im {S : Type} (a : Letter ℂ S) (h : a.pt.im = 0) : (ypt a).im = 0 := by
  unfold ypt
  split_ifs <;> simp [h]

theorem site_mem (P : Par) (i : Fin P.r) : siteA P i ∈ sitesFrom P 0 := by
  simp [sitesFrom, List.mem_ofFn]

end Mx9

open Mx9

theorem model_words_assemble : Formalism.FourierDecayAlt.M.ModelWordsAssemble := by
  intro hW hLS hSO hCh hLC P hP l S _ _ w hw
  refine ⟨fun i hi => hW.1 ℂ (A P) S (QQlev P l i) (qC P) w (hLS P hP l i hi) hw, ?_, ?_⟩
  · intro i
    have hσ := ((hSO P l).1 (siteA P i) (site_mem P i))
    refine hW.2.1 ℂ (A P) S (siteA P i) (QQlev P l (i + 1)) (QQlev P l i) w hσ.1 (hLC P l i) ?_ hw
    intro Y hY
    have h := (hCh P l).2 i Y
    rw [hY] at h
    exact h
  · intro Y hY hs z
    exact hW.2.2.2.1 ℂ (A P) S _ _ w Y (hSO P l) hw hY hs z

theorem cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut 1 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut (-1) (by norm_num) using 1 <;> push_cast <;> ring

theorem cut_admissible_base : Formalism.FourierDecayAlt.M.CutAdmBase := by
  intro hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  have key2 : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ((Y + 2 : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + 2) (hIS2 P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY 2 (by norm_num))
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : ypt a = (((ypt a).re : ℝ) : ℂ) := eq_ofReal (ypt_im a him)
  rw [hz]
  rcases hcut with hc | hc
  · refine ⟨?_, ?_, fun _ => ?_, qpos _ hc⟩
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key2 _ hc using 1 <;> push_cast <;> ring
  · refine ⟨?_, ?_, fun _ => ?_, ?_⟩
    · convert key _ hc (-1) (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert qsh _ hc using 2 <;> push_cast <;> ring

theorem model_assemble : Formalism.FourierDecayAlt.M.ModelAssemble := by
  intro hIS hQP hQS hCP hCPC hFA hFW hCD hLE hLS hSO hTy hR hCA P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAdm := hCA hIS hQP hQS hTy hR P hP l hl1 hlk S w hw
  obtain ⟨_, _, h3, h4, h5⟩ := hFW (A P) S P.r L (startM P l) w hst hstart hAdm
  refine ⟨hFA (A P) S P.r L (startM P l) w hst hstart hAdm, h3, h4, h5, ?_, ?_⟩
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPC hIS hQP hQS hCP S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e

theorem model_assemble_base : Formalism.FourierDecayAlt.M.ModelAssembleBase := by
  intro hIS hIS2 hQP hQS hCPB hCPCB hFAR hARB hWJ hCD hLE hLS hSO hTy hR hCAB P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAB := hCAB hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S w hw
  have hAR := hARB (A P) S P.r L (startM P l) w hAB
  have hF := hFAR (A P) S P.r L (startM P l) w hst hstart hAR
  obtain ⟨jRR, jTT, _, jN, jreg⟩ := hWJ (A P) S P.r L (startM P l) w
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← jRR, hF.form, FrameData.d, jN]
  · intro Y hY
    have h := hF.frame_τ Y (by rw [jreg]; exact hY)
    rwa [jTT] at h
  · intro Y hY hY1
    have h := hF.frame_l Y hY hY1
    rwa [jTT, FrameData.l] at h
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPCB hIS hQP hQS hCPB S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e

end Formalism.FourierDecayAlt.P
