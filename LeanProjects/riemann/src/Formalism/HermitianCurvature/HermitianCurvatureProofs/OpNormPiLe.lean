import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section norms

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem norm_gpsi (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  unfold G.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiStar (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + 0 + ρ) + k + 1) → ℂ) (ξ : U.Xi k p 0 ρ σ) :
    ‖U.psiStar k ρ σ z z' ξ‖ = 1 := by
  unfold U.psiStar U.psiH
  rw [norm_mul, norm_mul, norm_star, norm_psi, norm_psi, norm_gpsi, one_mul, one_mul]

theorem opNorm_pi_le (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z) : ‖Bs.π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [Bs.π_unitary h hh v, one_mul])

theorem opNorm_pi'_le (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z') : ‖Bs.π' h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [Bs.π'_unitary h hh v, one_mul])

theorem norm_pi_comp (Bs : B.RealPlaceData k ρ Wp Wq) {h : B.Mat k ρ} (hh : h ∈ UWset k ρ Bs.z) (A : Wq →L[ℂ] Wp) :
    ‖(Bs.π h).comp A‖ = ‖A‖ := by
  refine le_antisymm ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (opNorm_pi_le Bs hh) (norm_nonneg A))) ?_
  have hi : h⁻¹ ∈ UWset k ρ Bs.z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z).inv_mem h hh
  have hu : IsUnit h.det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z).unit h hh
  have e : A = (Bs.π h⁻¹).comp ((Bs.π h).comp A) := by
    rw [← ContinuousLinearMap.comp_assoc, ← Bs.π_rep.2 _ hi _ hh, Matrix.nonsing_inv_mul _ hu, Bs.π_rep.1]
    rfl
  calc ‖A‖ = ‖(Bs.π h⁻¹).comp ((Bs.π h).comp A)‖ := by rw [← e]
    _ ≤ ‖Bs.π h⁻¹‖ * ‖(Bs.π h).comp A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(Bs.π h).comp A‖ := mul_le_mul_of_nonneg_right (opNorm_pi_le Bs hi) (norm_nonneg _)
    _ = ‖(Bs.π h).comp A‖ := one_mul _

theorem sgs_mem {P : B.SS k ρ} (Bs : B.RealPlaceData k ρ Wp Wq) (hP : Bs.inSS P) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    B.sgs P g ∈ B.GV k ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  unfold B.sgs
  have g1 : (Matrix.of P.1.1 : B.Mat k ρ) ∈ B.GV k ρ := h1.1
  have g2 : (Matrix.of P.1.2 : B.Mat k ρ) ∈ B.GV k ρ := h2.1
  have g3 : (Matrix.of P.2.1 : B.Mat k ρ) ∈ B.GV k ρ := h3.1
  have g4 : (Matrix.of P.2.2 : B.Mat k ρ) ∈ B.GV k ρ := h4.1
  exact cG.mul_mem _ (cG.mul_mem _ (cG.mul_mem _ (cG.mul_mem _ (cG.inv_mem _ g1) _ (cG.inv_mem _ g2)) _ hg) _ g4) _ g3

theorem norm_fl_le (Bj : B.RealPlaceData k ρ Wp Wq) (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (q : B.SS k ρ × U.Xi k p 0 ρ σ)
    (hq : Bj.inSS q.1) :
    ‖FL Bj z0 z0' σ d H g q‖ ≤ ‖H (U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g))‖ := by
  unfold FL
  rw [norm_smul, norm_xiP, one_mul, norm_pi_comp Bj hq.1]
  have hi : (Matrix.of q.1.2.1 : B.Mat k ρ)⁻¹ ∈ UWset k ρ Bj.z' :=
    (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z').inv_mem _ hq.2.2.1
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_smul, norm_psiStar, one_mul]
  simpa using mul_le_mul_of_nonneg_left (opNorm_pi'_le Bj hi) (norm_nonneg (H _))

end norms

section main

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem ae_inSS (Bs : B.RealPlaceData k ρ Wp Wq) : ∀ᵐ P ∂Bs.μSS, Bs.inSS P := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarN
  have w3 := Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW'
  unfold B.RealPlaceData.μSS
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w3),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with P a b c e
  exact ⟨a, b, c, e⟩

theorem ae_goodL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) : ∀ᵐ x ∂(muL Bj σ), GoodL Bj σ x := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN
  unfold muL
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with x a b
  exact ⟨a, b⟩

theorem ae_goodR (Bj : B.RealPlaceData k ρ Wp Wq) : ∀ᵐ y ∂(muR (p := p) Bj), GoodR Bj y := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have w1 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW'
  have w2 := Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN
  unfold muR
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)] with x a b
  exact ⟨a, b⟩

theorem norm_cL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : ‖cL Bj σ x‖ = 1 := by
  unfold cL
  rw [norm_mul, norm_mul, norm_psi, norm_psi, norm_gpsi, one_mul, one_mul]

theorem norm_ellL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) (hx : GoodL Bj σ x)
    (A : Wq →L[ℂ] Wp) : ‖ellL Bj σ x A‖ = ‖A‖ := by
  unfold ellL
  rw [ContinuousLinearMap.smul_apply, norm_smul, norm_cL, one_mul, ContinuousLinearMap.compL_apply,
    norm_pi_comp Bj hx.1]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem core_main (hGS : GaXiSplit) (hPR : PsiRight) (hPA : PsiRnAct) (hPM : PsiMuP) (hRMP : RightMP)
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R)
    (hM1 : AEStronglyMeasurable (FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g)
      (Bj.μSS.prod (U.muXi k p 0 ρ σ)))
    (hM2 : AEStronglyMeasurable (fun q : XL k p ρ σ × XR k p ρ =>
      KrI B0 H (sxL Bj σ q.1 * U.mMap k p ρ (U.hMat σ d) g) (PsiR q.2)) ((muL Bj σ).prod (muR Bj)))
    (hM3 : ∀ x, GoodL Bj σ x →
      AEStronglyMeasurable (KrI B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) (B0.μW'.prod B0.μN))
    (hM4 : ∀ γ ∈ B.GV k ρ, Continuous (fun ξ : U.Xi k p 0 ρ σ =>
      U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ • H (U.gaXi k ρ σ d ξ (fun a => a.elim0) γ))) :
    Integrable (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) (muL Bj σ) ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ x, ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) ∂(muL Bj σ) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite Bj.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have : SigmaFinite (U.muXi k p 0 ρ σ) := by unfold U.muXi U.muXiH; infer_instance
  have : SigmaFinite (muL Bj σ) := by unfold muL; infer_instance
  have : SigmaFinite (muR (p := p) Bj) := by unfold muR; infer_instance
  have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
  have : BorelSpace ((U.LW σ → ℂ) × (G.UT p → ℂ)) := Prod.borelSpace
  have : BorelSpace (U.XiH p 0 σ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace (U.Xi k p 0 ρ σ) := Prod.borelSpace
  set x1 := U.mMap k p ρ (U.hMat σ d) g with hx1
  set F := FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g with hF
  obtain ⟨M, C, R', hM0, hball, hb⟩ := slice_bound hp σ d hd H hHc R hR
  have hgG : g ∈ B.GV k ρ := hg.1
  have hSS := ae_inSS Bj

  have hS1 : ∀ γ ∈ B.GV k ρ, Integrable (fun ξ : U.Xi k p 0 ρ σ =>
      U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ • H (U.gaXi k ρ σ d ξ (fun a => a.elim0) γ))
      (U.muXi k p 0 ρ σ) := by
    intro γ hγ
    refine hball.mono' (hM4 γ hγ).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [norm_smul, norm_psiStar, one_mul]
    refine (hb ξ _ γ hγ).trans ?_
    have h1 := bumpG_le_one R' γ
    have h2 : 0 ≤ M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ :=
      mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    nlinarith [bumpG_nonneg R' γ]

  have hbi : Integrable (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => bumpG R' (B.sgs q.1 g) *
      (M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) q.2))
      (Bj.μSS.prod (U.muXi k p 0 ρ σ)) := (bump_int Bj hg R').mul_prod hball
  have hFi : Integrable F (Bj.μSS.prod (U.muXi k p 0 ρ σ)) := by
    refine hbi.mono' hM1 ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hSS] with q hq
    refine (norm_fl_le Bj _ _ σ d H g q hq).trans ((hb q.2 _ _ (sgs_mem Bj hq hgG)).trans (le_of_eq ?_))
    ring

  have hL : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, F q ∂(Bj.μSS.prod (U.muXi k p 0 ρ σ)) := by
    rw [integral_prod F hFi]
    show ∫ P, JF.integrand Bj _ g P ∂Bj.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [hSS] with P hP
    have hI := hS1 _ (sgs_mem Bj hP hgG)
    set L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := JF.xiP Bj P •
      ((ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of P.1.1))).comp
        ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Bj.π' (Matrix.of P.2.1)⁻¹))) with hLdef
    have e1 : ∀ ξ, F (P, ξ) = L (U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ξ •
        H (U.gaXi k ρ σ d ξ (fun a => a.elim0) (B.sgs P g))) := fun ξ => rfl
    simp_rw [e1]
    rw [L.integral_comp_comm hI]
    rfl

  have hmp := splitE_mp Bj σ
  have hS4 : ∫ q, F q ∂(Bj.μSS.prod (U.muXi k p 0 ρ σ)) =
      ∫ z, F ((splitE σ).symm z) ∂((muL Bj σ).prod (muR Bj)) :=
    ((hmp.symm (splitE σ)).integral_comp' F).symm

  have hgood : ∀ᵐ z ∂((muL Bj σ).prod (muR (p := p) Bj)), GoodL Bj σ z.1 ∧ GoodR Bj z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_goodL Bj σ),
      Measure.quasiMeasurePreserving_snd.ae (ae_goodR (p := p) Bj)] with z a b
    exact ⟨a, b⟩
  set GRl : XL k p ρ σ × XR k p ρ → (Wq →L[ℂ] Wp) := fun z => ellL Bj σ z.1 (KrI B0 H (sxL Bj σ z.1 * x1) (PsiR z.2))
    with hGRl
  set GR0 : XL k p ρ σ × XR k p ρ → (Wq →L[ℂ] Wp) := fun z => KrI B0 H (sxL Bj σ z.1 * x1) (PsiR z.2) with hGR0
  have hS5 : (fun z => F ((splitE σ).symm z)) =ᵐ[(muL Bj σ).prod (muR Bj)] GRl := by
    filter_upwards [hgood] with z hz
    obtain ⟨x, y⟩ := z
    exact fl_split hGS hPR hPA hPM Bj B0 hz' hπ' σ d H g x y hz.1 hz.2

  have hFi' : Integrable (fun z => F ((splitE σ).symm z)) ((muL Bj σ).prod (muR Bj)) :=
    ((hmp.symm (splitE σ)).integrable_comp_emb (splitE σ).symm.measurableEmbedding).2 hFi
  have hGRli : Integrable GRl ((muL Bj σ).prod (muR Bj)) := hFi'.congr hS5
  have hGR0i : Integrable GR0 ((muL Bj σ).prod (muR Bj)) := by
    refine hGRli.norm.mono' hM2 ?_
    filter_upwards [hgood] with z hz
    rw [hGRl, hGR0]
    simp only
    rw [norm_ellL Bj σ z.1 hz.1]

  have hRM := hRMP k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
  have hmap : (muR (p := p) Bj).map PsiR = B0.μW'.prod B0.μN := by
    rw [hN0]
    unfold muR
    rw [hNj]
    exact hRM.map_eq
  have hPm : Measurable (PsiR (k := k) (p := p) (ρ := ρ)) := hRM.measurable
  have hS7 : ∀ x, GoodL Bj σ x → PBG.Kr B0 H (sxL Bj σ x * x1) = ∫ y, GR0 (x, y) ∂(muR Bj) := by
    intro x hx
    have hA : AEStronglyMeasurable (KrI B0 H (sxL Bj σ x * x1)) ((muR (p := p) Bj).map PsiR) := by
      rw [hmap]; exact hM3 x hx
    rw [kr_eq_int, ← hmap, integral_map hPm.aemeasurable hA]

  have hS8 : ∀ᵐ x ∂(muL Bj σ), ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * x1)) = ∫ y, GRl (x, y) ∂(muR Bj) := by
    filter_upwards [ae_goodL Bj σ, hGR0i.prod_right_ae] with x hx hxi
    rw [hS7 x hx, ← (ellL Bj σ x).integral_comp_comm hxi]
  refine ⟨hGRli.integral_prod_left.congr (hS8.mono fun x hx => hx.symm), ?_⟩
  rw [integral_congr_ae hS8, ← integral_prod GRl hGRli, ← integral_congr_ae hS5, ← hS4, ← hL]

end main

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
