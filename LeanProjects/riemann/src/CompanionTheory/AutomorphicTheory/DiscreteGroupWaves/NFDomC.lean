import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFMainS
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFCoreC

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfTopDomAll_of_ptwC (hP : NFDomPtwC) (hJ : NFJCutFF) : NFTopDomAll := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := dominated_L2_truncation_bound_holds Cb C₁
  obtain ⟨C3, H3⟩ := domination_measurability_holds Cb
  obtain ⟨C4, H4⟩ := limit_of_module_forms Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have m1 := nfHyp_monoC hH (le_max_of_le_left (le_max_left C1 C2))
  have m2 := nfHyp_monoC hH (le_max_of_le_left (le_max_right C1 C2))
  have m3 := nfHyp_monoC hH (le_max_of_le_right (le_max_left C3 C4))
  have m4 := nfHyp_monoC hH (le_max_of_le_right (le_max_right C3 C4))
  obtain ⟨hχ, hCb, hf, hfA, -, hN2⟩ := hH
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  choose hh hhi hhb using fun t => H2 Wp Wq P p f A₀ p₀ χ N m2 (Th t) (hok t)
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => H3 Wp Wq P p f A₀ p₀ χ Y N m3 w hw hN ε hε,
    fun c => Mb * ∑ t, |hh t c|, (integrable_finsetSum Finset.univ fun t _ => (hhi t).abs).const_mul Mb,
    eventually_nhdsWithin_of_forall fun ε hε => ?_⟩
  have hε' : 0 < ε := hε
  obtain ⟨-, hlim⟩ := H4 Wp Wq P p _ χ ε _ N (cutN P.k P.r) hCb hχ hε' (ckOn_fpm p p₀ hf hid)
    (inCC_fpm_id p p₀ hfA) m4.2.2.2.2.1 (fun _ _ => rfl)
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun t => hhb t n] with c hc
  by_cases hc' : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [domination_at_zero_holds Wp Wq P p _ w c hc', norm_zero]
    exact mul_nonneg hMb (Finset.sum_nonneg fun t _ => abs_nonneg _)
  have hT : Tendsto (fun n => ‖topD p (apx (D.cutF p.T.base χ
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) w c‖) atTop
      (𝓝 ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c‖) := by
    refine Tendsto.norm ?_
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp ((hlim (P.r + 1) w hw.1 hN _ _).const_mul _)
  refine le_of_tendsto' hT fun n => ?_
  set η : ℝ := TBB.Gp p (TBB.bigPt P.r c) / 2 with hη
  have hη0 : 0 < η := half_pos hc'.2
  have hηG : η < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c) := half_lt_self hc'.2
  set f' : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun g => cutN P.k P.r n g • D.cutF p.T.base χ f η g with hf'
  have hcp : KB.CptCoef p.T.base f' := cptCoef_apx P p.T.base hχ hf hη0 n
  obtain ⟨_, -, hnice⟩ := PBL.nice_of_cpt hcp
  have hb' := hb f' A₀ ⟨hχ, hCb, hcp.1, fun m => hnice.2.1 A₀ m, m1.2.2.2.2.1, hN2⟩ hcp
    (hJ Wp Wq P p _ (JCTx6.Link2.ckOn_cutF p.T.base hχ hf η) n) ε hε' c hc'.1 hc'.2
  have eL : D.cutF p.T.base χ (TBBx4.fpm p f' (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      D.cutF p.T.base χ (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) η := by
    funext g
    simp only [hf', apx, D.cutF, TBBx4.fpm, ContinuousLinearMap.smul_comp, smul_smul]
    congr 1
    ring
  have eL' : topD p (D.cutF p.T.base χ (TBBx4.fpm p f' (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c =
      topD p (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) w c := by
    rw [eL]
    unfold topD TBB.Ew TBB.NP
    rw [rrTop_cutF_eq p hCb hχ (cptCoef_apx P p.T.base hχ (ckOn_fpm p p₀ hf hid) hε' n).1 hη0 hw.1 _ (Or.inr hηG)]
  rw [eL'] at hb'
  refine hb'.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) hMb)
  have eR : TBB.Ew p (fun _ => 1) (B.opApply (Th t) f') (P.r + 1) [] (TBB.bigPt P.r c) =
      TBB.Ew p (fun _ => 1) (B.opApply (Th t) (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) := by
    rw [TBBx2.Tri.Ew_top p _ hc'.1, TBBx2.Tri.Ew_top p _ hc'.1]
    congr 4
    refine vecV_congr_gt _ _ _ _ η (fun g _ hg => ?_) (Or.inr hηG)
    refine JCTx6.Pos.opApply_congr_open (Th t) (O := {x | η < Gf P.k P.r p.T.base.z p.T.base.z' x})
      (isOpen_lt continuous_const (JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous) (fun x hx => ?_) g hg
    simp only [hf', D.cutF]
    rw [hχ.2.2 _ ((one_le_div hη0).2 (le_of_lt hx))]
    simp
  rw [eR]
  exact (hc n t).trans (le_abs_self _)

theorem nfTopDomAll_of_C (hT : NFTieHatC) (hH : NFHatProdKBS) (hJ : NFJCutFF) : NFTopDomAll :=
  nfTopDomAll_of_ptwC (nfDomPtwC_of_open hT hH) hJ

end

end CompanionTheory.NFCpt
