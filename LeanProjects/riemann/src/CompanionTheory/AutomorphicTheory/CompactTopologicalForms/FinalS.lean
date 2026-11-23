import Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCopy2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.JacobiFieldSquareIntegrable
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopFormCpt

namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFTopDomAllJ : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → B.JF p.T.base f ∈ FFKB p → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopDom p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

theorem nfTopDomAllJ_of_cut (hZ : NFDomZero) (hP : NFDomPtwS) (hL : DominatedL2OperatorBound) (hM : NFDomMeas) : NFTopDomAllJ := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := hL Cb C₁
  obtain ⟨C3, H3⟩ := hM Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH hJ w hw hN
  have mono : ∀ c, c ≤ max C1 (max C2 C3) → NFHyp Cb c p f A₀ p₀ χ N := fun c hc => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hc hX
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  have hb := hb f A₀ (mono C1 (le_max_left _ _)) hJ
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε =>
      H3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (le_trans (le_max_right _ _) (le_max_right _ _))) w hw hN ε hε,
    fun c => Mb * ∑ t, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
      TBB.Ew p (fun _ => 1) (B.opApply (Th t) f) (P.r + 1) [] (TBB.bigPt P.r c), ?_, ?_⟩
  · exact (integrable_finsetSum Finset.univ fun t _ =>
      H2 Wp Wq P p f A₀ p₀ χ N (mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))) (Th t) (hok t)).const_mul Mb
  · refine eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hb ε hε c hc.1 hc.2
    · rw [hZ Wp Wq P p _ w c hc, norm_zero]
      exact mul_nonneg hMb (Finset.sum_nonneg fun t _ =>
        mul_nonneg (pow_nonneg (norm_nonneg _) _) (TBBx4.ew_nonneg p _ _))

theorem nfTopDomAllJ_of_open (hT : NFTieHatS) (hH : NFHatProdKBS) : NFTopDomAllJ :=
  nfTopDomAllJ_of_cut domination_at_zero_holds (nfDomPtwS_of_open leibniz_vector_estimate_holds (nFCoreNS_of_open leibniz_vector_estimate_holds hT hH))
    dominated_L2_operator_bound_holds domination_measurability_holds

theorem blockGrowthBound_apx_cutF (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hχ : C6.IsCut0 χ)
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hnn : ∀ y, 0 < nn y) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
  block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem limEvT_J (hA : P5.ThmPActualCpt) (h3 : NFTopDomAllJ) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → B.JF p.T.base f ∈ FFKB p →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, H1⟩ := CompanionTheory.NFCpt.top_form_all_compact hA Cb
  obtain ⟨C2, H2⟩ := top_pointwise_all_levels_holds Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  refine ⟨max (max C1 C2) (max C3 100), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH hJ w hw hN
  have m1 : C1 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_left _ _)
  have m4 : 100 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_right _ _)
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hL := fun (χ' : ℝ → ℝ) (hχ' : C6.IsCut0 χ') => CompanionTheory.BpCpt.NFId.lim_top p
    (H1 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m1 hχ') w hw hN)
    (H2 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m2 hχ') w hw hN)
    (H3 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m3 hχ') hJ w hw hN)
  have hId := CompanionTheory.BpCpt.NFId.nfTopId_of_lim p hH.1 (ckOn_fpm p p₀ hH.2.2.1 hid) (inCC_fpm_id p p₀ hH.2.2.2.1) hw.1
    (CutMP.ER.bound_aux P.r P.k w.length N _ hN (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m4 hH.1).2.2.2.2.1) hL
  unfold NFTopId at hId
  rw [← hId]
  exact hL χ hH.1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_J (h3 : NFTopDomAllJ)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_J hA h3 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hJ hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    (blockGrowthBound_apx_cutF hA p nn χ _ Y K N Cb hCb hχ (ckOn_fpm p p₀ hf hid) hnn)
    (hn Wp Wq P p f A₀ p₀ χ Y N ⟨hχ, hCb, hf, hfA, hth4, hN2⟩ hJ) hBd

end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eqR_J (h3 : NFTopDomAllJ)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF S.pp.T.base (fun g => (f g).comp (S.Ap g)) ∈ FFKB S.pp →
      B.JF S.pm.T.base (fun g => (f g).comp (S.Am g)) ∈ FFKB S.pm →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ :=
    thmBpAt_eq_limEvTCpt hA Formalism.FourierDecayAlt.P.CutBP2.normaliser_across_places Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_J hA h3 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hJp hJm hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hBdp hBdm
  have hI5p := blockGrowthBound_apx_cutF hA S.pp nnp χ _ Yp K N Cb hDDp hχ (ckOn_fpmSh S.pp p₀ hf (ckOn_of_polyOp S.polyP)) hnnp
  have hI5m := blockGrowthBound_apx_cutF hA S.pm nnm χ _ Ym K N Cb hDDm hχ (ckOn_fpmSh S.pm p₀ hf (ckOn_of_polyOp S.polyM)) hnnm
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hLp : LimEvT S.pp χ (fpmSh S.pp f S.Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm S.pp f S.Ap p₀
    have k := hn Wp S.Wqp (shP P S.up S.up') S.pp (fun g => (f g).comp (S.Ap g)) (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp S.polyP), inCC_compSh S.pp hfA S.polyP, hth4', hN2⟩ hJp
    exact Eq.mpr (congrArg (fun F => LimEvT S.pp χ F Yp N) e) k
  have hLm : LimEvT S.pm χ (fpmSh S.pm f S.Am p₀) Ym N := by
    have e := fpmSh_eq_fpm S.pm f S.Am p₀
    have k := hn Wp S.Wqm (shP P S.um S.um') S.pm (fun g => (f g).comp (S.Am g)) (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp S.polyM), inCC_compSh S.pm hfA S.polyM, hth4', hN2⟩ hJm
    exact Eq.mpr (congrArg (fun F => LimEvT S.pm χ F Ym N) e) k
  exact h P Wp Wq S.Wqp S.Wqm S.up S.up' S.um S.um' p S.pp S.pm f S.Ap S.Am S.ApPt S.AmPt b Λ
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ)) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ S.hzp S.hzp' S.hzm
    S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP) (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
