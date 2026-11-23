import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopSq

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

theorem uInv_at_zero {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv 0 w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    simp only [KB.uInv, uInv_at_zero w, map_zero, ite_self, zero_smul, add_zero]
    split_ifs with h
    · congr 1
      funext a
      induction a using Fin.cases with
      | zero => exact h.symm
      | succ i => rfl
    · congr 1
      funext a
      induction a using Fin.cases with
      | zero =>
        have h1 : e (0 : Fin (w.length + 1)) = 1 := by
          rcases Fin.exists_fin_two.1 ⟨e (0 : Fin (w.length + 1)), rfl⟩ with h0 | h0
          · exact absurd h0 h
          · exact h0
        exact h1.symm
      | succ i => rfl

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem waveG_at_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp [KB.waveG, P5.fsv, uInv_at_zero]

theorem ew_snoc (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) {j : ℕ} (hj : j ≤ P.r)
    {h : C.LPt} (hh : D.IsLocPt h j) (c : ℂ) :
    TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
      ((KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])).re := by
  have hN : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  have hA : 0 ≤ A := PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [PBD.weight_product_append, hh.2, hAdef, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.Ew TBB.NP
  rw [hn, hN, div_one, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    ring

theorem ew_low (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) {j : ℕ} (hj : j ≤ P.r)
    {h : C.LPt} (hh : D.IsLocPt h j) :
    TBB.Ew p (fun _ => 1) F j w h = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (p.RR F j w h h).re := by
  have hN : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  have hA := PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl (by rw [hh.2]; omega)
  unfold TBB.Ew TBB.NP TBB.nPt
  rw [hN, div_one, Complex.re_ofReal_mul,
    PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega), Real.mul_self_sqrt hA]

theorem ew_step (hPS : StandardPairingDecay.PStdC) (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) {j : ℕ} (hj : j ≤ P.r) {h : C.LPt} (hh : D.IsLocPt h j) :
    Integrable (fun c : ℂ => TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) = TBB.Ew p (fun _ => 1) F j w h := by
  obtain ⟨φ, -, hφi, hφ, hint⟩ := hPS Wp Wq P p F j hj w h h hh hh Cb hCb hF hw
  have hae : (fun c : ℂ => C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (φ c).re) =ᵐ[volume]
      fun c : ℂ => TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) := by
    filter_upwards [ae_ne_zero_c] with c hc
    rw [ew_snoc p F w hj hh c, hφ c hc]
  refine ⟨(hφi.re.const_mul _).congr hae, ?_⟩
  have h0 := hint 0
  rw [waveG_at_zero, ← PBL.rr_eq_form p F j hj w h h hh hh] at h0
  simp only [P5.fsv, zero_mul, map_zero, sub_self, Complex.exp_zero, one_mul] at h0
  rw [← integral_congr_ae hae, integral_const_mul, ew_low p F w hj hh, ← h0]
  congr 1
  exact integral_re hφi

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ a, c a ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := PBJ.Dens.isLocPt_bigPt c hc

theorem topForm_cpt (hPS : StandardPairingDecay.PStdC) (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) :
    Integrable (topD p F w) ∧ ∫ c, topD p F w c = (p.RR F 0 w [] []).re := by
  have h := tower_integral (P.r + 1)
    (fun j c => TBB.Ew p (fun _ => 1) F j w (List.ofFn fun l => ((1 : ℕ), c l)))
    (topD_aesm p hCb hw hF) (fun c _ => ew_top_nonneg p F w _) (fun j hj c hc => by
      have e : ∀ t : ℂ, (List.ofFn fun l : Fin (j + 1) => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l)) =
          (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
        intro t
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      simp only [e]
      exact ew_step hPS p hCb hw hF (by omega) (isLocPt_ofFn c hc))
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [List.ofFn_zero]
  rw [TBBx3.ew_zero_nil]
  simp [TBB.normC]

end

end CompanionTheory.NFCpt
