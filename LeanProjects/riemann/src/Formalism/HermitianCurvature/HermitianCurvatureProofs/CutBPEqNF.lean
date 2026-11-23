import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem fpmSh_eq_fpm (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (p₀ : ℕ) :
    fpmSh q f A p₀ = TBBx4.fpm q (fun g => (f g).comp (A g)) (fun _ => ContinuousLinearMap.id ℂ Wq') p₀ := by
  first
  | rfl
  | (unfold fpmSh; rfl)
  | unfold fpmSh

theorem inCC_compSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} {A₀ : ℝ} {d : ℕ} (hf : ∀ m : ℕ, B.InCC A₀ m f) (hA : PolyOp d A) :
    ∀ m : ℕ, B.InCC (A₀ - d) m (fun g => (f g).comp (A g)) := by
  intro m
  have h := shifted_decay P Wp Wq Wq' u u' q f A A₀ d 0 hf hA m
  simp only [mul_zero, Nat.cast_zero, sub_zero] at h
  first
  | exact h
  | (convert h using 2; rw [fpmSh_eq_fpm]; simp [TBBx4.fpm])
  | (convert h using 2; rw [fpmSh_eq_fpm]; unfold TBBx4.fpm)

end sh

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ptBound_main_limEvT (hA : P5.ThmPActual) (Cb : ℝ) : ∃ C₂ c₃ Cc Cc' : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (q : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P q.l0 q.T.base Cb q.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      TBBx5.WaveGrid q nn Y Λ K N → TBBx5.LiftGrid q nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound q nn (apx (D.cutF q.T.base χ F ε) n) Y K N) →
      LimEvT q χ F Y N →
      LimBd q nn F Y N → TBB.PtBound q F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_dec_all hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  obtain ⟨Cc', hE⟩ := limE_of_limEvT hA Cb
  refine ⟨C₂, c₃, Cc, Cc', hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth1 hth2 hth3 hWG hLG hI5 hLim hBd
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCc Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA hth2)
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA hth3 hLim hBd)
    (lemB_one q F)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq_limEvT (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
      [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
      (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
      (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₁ : ℝ) (n₀ p₀ : ℕ)
      (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
      pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      (∀ m : ℕ, B.InCC A₁ m (fpmSh pp f Ap p₀)) → (∀ m : ℕ, B.InCC A₁ m (fpmSh pm f Am p₀)) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₁ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N →
      TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) →
      LimEvT pp χ (fpmSh pp f Ap p₀) Yp N →
      LimEvT pm χ (fpmSh pm f Am p₀) Ym N →
      LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, c₃, Cc, Cc', hC₂, hPt⟩ := ptBound_main_limEvT hA Cb
  obtain ⟨C₄, hC₄⟩ := thmBpOfPartsSh C₃ CΛ C₀ C₂ 0 hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₁ n₀ p₀ χ nnp nnm
    Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hAp hAm hdp hdm hth1 hth2
    hth3 hAms hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := hN P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀ hzp hzp' hzm hzm' hAms
  have hReg := Formalism.FourierDecayAlt.P.regularity_at_place p f b C₃ (2 * p₀ + n₀) (by linarith) hexp
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ A₁ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf hAp) hdp hth1 hth2 hth3 hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ A₁ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf hAm) hdm hth1 hth2 hth3 hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ 1 n₀ p₀ hb hΛ hΛb one_pos (by simp) hT hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq_NF (hA : P5.ThmPActual) (h1 : NFTopFormAll) (h2 : NFTopPtwAll) (h3 : NFTopDomAll)
    (h4 : NFTopIdAll) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAt p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pp nnp (apx (D.cutF S.pp.T.base χ (fpmSh S.pp f S.Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pm nnm (apx (D.cutF S.pm.T.base χ (fpmSh S.pm f S.Am p₀) ε) n) Ym K N) →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ :=
    thmBpAt_eq_limEvT hA Formalism.FourierDecayAlt.P.CutBP2.normaliser_across_places Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NF hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hI5p hI5m hBdp hBdm
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - n₀) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hLp : LimEvT S.pp χ (fpmSh S.pp f S.Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm S.pp f S.Ap p₀
    have k := hn Wp S.Wqp (shP P S.up S.up') S.pp (fun g => (f g).comp (S.Ap g)) (A₀ - n₀) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp S.polyP), inCC_compSh S.pp hfA S.polyP, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT S.pp χ F Yp N) e) k
  have hLm : LimEvT S.pm χ (fpmSh S.pm f S.Am p₀) Ym N := by
    have e := fpmSh_eq_fpm S.pm f S.Am p₀
    have k := hn Wp S.Wqm (shP P S.um S.um') S.pm (fun g => (f g).comp (S.Am g)) (A₀ - n₀) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp S.polyM), inCC_compSh S.pm hfA S.polyM, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT S.pm χ F Ym N) e) k
  exact h P Wp Wq S.Wqp S.Wqm S.up S.up' S.um S.um' p S.pp S.pm f S.Ap S.Am S.ApPt S.AmPt b Λ
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ S.hzp S.hzp' S.hzm
    S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP) (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ n₀ p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ n₀ p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq
