import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.TopDensityBound

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_comp_sq_le (E : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (E.comp X)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact E.le_opNorm _

variable {P : M.Par}

theorem V_eq_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (h : ¬ 0 < TBB.Gp p γ) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dif_neg]
  exact fun h' => h h'.2

theorem RR_cons (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (hw : w ≠ [])
    {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR F (P.r + 1) w γ γ = ((∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
      Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e F) γ))‖ ^ 2 : ℝ) : ℂ) := by
  have : p.RR F (P.r + 1) w γ γ = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w γ γ := by
    simp [KB.Pl.RR, D.RRplace, hγ, hw]
  rw [this]
  unfold Top.topOf
  push_cast
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  simp only [TBB.TTp, KB.Pl.V]
  push_cast
  ring

theorem Ew_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) w γ =
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)) *
        (p.RR F (P.r + 1) w γ γ).re := by
  unfold TBB.Ew TBB.NP TBB.normC
  rw [Complex.re_ofReal_mul]
  simp

theorem ne_zero_of_isLocPt {r : ℕ} (c : Fin (r + 1) → ℂ) (h : D.IsLocPt (TBB.bigPt r c) (r + 1)) (l : Fin (r + 1)) :
    c l ≠ 0 := by
  have := h.1 (1, c l) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨l, rfl⟩)
  exact this.2

theorem wPt_bigPt (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) = ‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c) := by
  unfold Top.wPt TBB.Gp
  have h : D.ptMatN (TBB.bigPt P.r c) (P.r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Complex.normSq_eq_norm_sq]

end aux

theorem top_density_le : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬((∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = 0) ∧ ((∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) ∧ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) = TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 ∧ |TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)| ≤ C * TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * (‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length * ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) := by
  intro Wp Wq _ _ _ _ _ _ P p w
  set K : Ix (Fin w.length) → ℝ := fun e => ∑ ρ : M.Ty P, |(Top.cW P p.l0 w e ρ).re| * ‖p.TP.E ρ‖ ^ 2 with hK
  have hK0 : ∀ e, 0 ≤ K e := fun e => Finset.sum_nonneg fun ρ _ => by positivity
  have hS0 : 0 ≤ ∑ e, K e := Finset.sum_nonneg fun e _ => hK0 e
  refine ⟨1 + ∑ e, K e, by linarith, fun H c => ⟨fun hn => ?_, fun hc hG => ?_⟩⟩
  · rw [Ew_eq]
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := fun h => hn ⟨ne_zero_of_isLocPt c hl, h⟩
      by_cases hw : w = []
      · subst hw
        rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top p H hl, V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self,
          Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
        simp
      · rw [RR_cons p H w hw hl]
        simp [V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
    · have : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) = 0 := by
        simp [KB.Pl.RR, D.RRplace, hl]
      rw [this]; simp
  · have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
    have hn : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) := by
      unfold TBB.TTp
      rw [Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt _ _ _ _ c hζ.le]
      exact Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _
    have hnil : TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) =
        TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
      rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hl, Real.mul_self_sqrt hn]
    refine ⟨hn, hnil, ?_⟩
    by_cases hw : w = []
    · subst hw
      rw [hnil, abs_of_nonneg (by positivity)]
      simp only [p.Θ.nil, List.length_nil, pow_zero, mul_one]
      rw [Finset.sum_const]
      have hcard : (Finset.univ : Finset (Ix (Fin 0))).card = 1 := by simp [Ix]
      rw [hcard, one_smul]
      have : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
        positivity
      rw [mul_assoc]
      exact le_mul_of_one_le_left this (le_add_of_nonneg_right hS0)
    · rw [Ew_eq, Real.mul_self_sqrt hn, RR_cons p H w hw hl, Complex.ofReal_re, abs_of_nonneg (by positivity),
        ← wPt_bigPt]
      set Wt := Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) with hWt
      have hW0 : 0 ≤ Wt := by rw [hWt, wPt_bigPt]; positivity
      have key : (∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
          Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
            ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2) ≤
          (1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        set v := ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 with hv
        have hv0 : 0 ≤ v := by positivity
        have hKe : K e ≤ 1 + ∑ e, K e := by
          have := Finset.single_le_sum (f := K) (fun e _ => hK0 e) (Finset.mem_univ e)
          linarith
        calc _ ≤ K e * Wt ^ w.length * v := by
              simp only [hK]
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_le_sum fun ρ _ => ?_
              have h1 : Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 ≤
                  Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re| := by
                unfold Top.dH
                rw [← hWt, Real.sq_sqrt']
                exact max_le (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
              have h2 := hsVec_comp_sq_le (p.TP.E ρ) (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))
              calc _ ≤ (Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re|) * (‖p.TP.E ρ‖ ^ 2 * v) :=
                    mul_le_mul h1 h2 (by positivity) (by positivity)
                _ = _ := by ring
          _ ≤ _ := by gcongr
      calc _ ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ((1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left key hn
        _ = _ := by ring

end GlobalTheory.TopDensityBound
