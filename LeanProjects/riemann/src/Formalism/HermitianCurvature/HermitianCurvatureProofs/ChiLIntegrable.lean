import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiCStarMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section inst

variable {k r : ℕ} (σ : Equiv.Perm (Fin r))

instance borelRC : BorelSpace (U.RC k r 0) := Prod.borelSpace

instance borelXiH : BorelSpace (U.XiH r 0 σ) := by
  have : BorelSpace ((U.LW σ → ℂ) × (G.UT r → ℂ)) := Prod.borelSpace
  have : BorelSpace ((Fin 0 → Fin r → ℂ) × (Fin r → Fin 0 → ℂ)) := Prod.borelSpace
  exact Prod.borelSpace

instance borelXi : BorelSpace (U.Xi k r 0 0 σ) := by
  have : BorelSpace (U.RC k r 0 × U.RC k r 0) := Prod.borelSpace
  have := borelXiH (r := r) σ
  exact Prod.borelSpace

end inst

section cont

variable {k r : ℕ}

theorem lowS_cont (w : Equiv.Perm (Fin r)) : Continuous (StabilizerDisintegration.lowS w) := by
  unfold StabilizerDisintegration.lowS C2.lowOf
  refine continuous_const.add ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun q _ => ?_
  split_ifs
  · exact continuous_apply q
  · exact continuous_const

theorem Amat_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : Continuous (Amat σ d) := by
  unfold Amat
  exact (continuous_const.matrix_mul (lowS_cont σ.symm)).matrix_mul continuous_const

theorem Amat_inv_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) :
    Continuous fun x => (Amat σ d x)⁻¹ := by
  have e : (fun x => (Amat σ d x)⁻¹) = fun x => (Amat σ d x).adjugate := by
    funext x; exact Dx2.SL.inv_adj _ (StabilizerDisintegration.UC.det_UT (conjS_UT hd x))
  rw [e]; exact (Amat_cont σ d).matrix_adjugate

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : B.Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi; rw [Complex.norm_exp]; simp

theorem norm_Gpsi (β x : ℂ) : ‖G.psi β x‖ = 1 := by
  unfold G.psi; rw [Complex.norm_exp]; simp

theorem norm_psiStar (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) (ξ : U.Xi k r 0 0 σ) :
    ‖U.psiStar k 0 σ z z' ξ‖ = 1 := by
  rw [psiStar_zero, norm_mul, norm_mul, norm_psi, norm_star, norm_psi, norm_Gpsi]; norm_num

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous fun g : B.Mat k r => psi k r z c g := by
  unfold psi ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finsetSum _ fun a _ => ?_
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · fun_prop

theorem psiStar_cont (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) :
    Continuous (U.psiStar k 0 σ z z') := by
  have e : U.psiStar k 0 σ z z' = fun ξ : U.Xi k r 0 0 σ => psi k r z cStd (U.Rn k r 0 ξ.1.1) *
      star (psi k r z' cStd (U.Rn k r 0 ξ.1.2)) *
      G.psi U.betaU (U.subS (U.wP σ * U.lowW σ ξ.2.2.1 * (U.wP σ)⁻¹) + U.supS (G.upper ξ.2.2.2)) := by
    funext ξ; exact psiStar_zero σ z z' ξ
  rw [e]
  refine ((((psi_cont z cStd).comp ((Dx2.SplitF.rn_cont r 0).comp (continuous_fst.comp continuous_fst))).mul
    (continuous_star.comp ((psi_cont z' cStd).comp ((Dx2.SplitF.rn_cont r 0).comp
      (continuous_snd.comp continuous_fst))))).mul ?_)
  unfold G.psi
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (Continuous.add ?_ ?_)))))
  · unfold U.subS
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · exact ((((continuous_const.matrix_mul ((Dx2.SL.cont_lowW σ).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))).matrix_mul continuous_const)).matrix_elem _ _)
    · exact continuous_const
  · unfold U.supS
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · exact ((StabilizerDisintegration.UC.cont_upper.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_elem _ _)
    · exact continuous_const

def gaX (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (γ : B.Mat k 0) (ξ : U.Xi k r 0 0 σ) : B.Mat k (r + 0 + 0) :=
  U.gaXi k 0 σ d ξ (fun a => a.elim0) γ

theorem gaX_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) (γ : B.Mat k 0) :
    Continuous (gaX σ d γ) := by
  have h := (gaXi_cont (k := k) σ d hd).comp (Continuous.prodMk_left (X := U.Xi k r 0 0 σ) γ)
  exact h

theorem FgaX_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ)
    (hd : ∀ i, d i ≠ 0) (F : B.Mat k r → E) (hFc : ContinuousOn F (B.GV k r)) (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) :
    Continuous fun ξ : U.Xi k r 0 0 σ => F (gaX σ d γ ξ) := by
  have hm : ∀ ξ : U.Xi k r 0 0 σ, gaX σ d γ ξ ∈ B.GV k (r + 0 + 0) := fun ξ => gaXi_mem_GV σ d hd ξ γ hγ
  have h := ContinuousOn.comp_continuous (f := gaX σ d γ) (s := B.GV k (r + 0 + 0)) hFc (gaX_cont σ d hd γ) hm
  exact h

instance muXi_sfinite (σ : Equiv.Perm (Fin r)) : SFinite (U.muXi k r 0 0 σ) := by
  unfold U.muXi; infer_instance

end cont

section inner

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

def conjL (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (S.π (Matrix.of h))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (S.π' (Matrix.of h')⁻¹))

theorem conjL_apply (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) (X : Wq →L[ℂ] Wp) :
    conjL S h h' X = (S.π (Matrix.of h)).comp (X.comp (S.π' (Matrix.of h')⁻¹)) := rfl

theorem norm_conjL_le (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z)
    (hh' : Matrix.of h' ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) : ‖conjL S h h' X‖ ≤ ‖X‖ := by
  rw [conjL_apply]
  have h1 : ‖S.π (Matrix.of h)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [S.π_unitary _ hh v, one_mul]
  have hi : (Matrix.of h')⁻¹ ∈ UWset k r S.z' := WeylGroupFacts.uw_inv hh'
  have h2 : ‖S.π' (Matrix.of h')⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [S.π'_unitary _ hi v, one_mul]
  calc ‖(S.π (Matrix.of h)).comp (X.comp (S.π' (Matrix.of h')⁻¹))‖
      ≤ ‖S.π (Matrix.of h)‖ * (‖X‖ * ‖S.π' (Matrix.of h')⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * 1) := by gcongr
    _ = ‖X‖ := by ring

theorem chiL_integrable (w0 : Equiv.Perm (Fin r)) : Integrable (chiL w0) := by
  unfold chiL
  refine (integrableOn_const (C := (1 : ℝ)) ?_).integrable_indicator (MeasurableSet.univ_pi fun _ => boxC_meas)
  rw [volume_pi, Measure.pi_pi]
  simp [boxC_vol]

set_option maxHeartbeats 1000000 in

theorem inner_int (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ)
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z') :
    Integrable (fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2))))
        ((QN k r).prod (QN k r)) ∧
      ∫ q, theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2)))
        ∂((QN k r).prod (QN k r)) =
        conjL S h h' (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h'))) ∧
      ∫ q, ‖theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2)))‖
        ∂((QN k r).prod (QN k r)) ≤ M * (U.muXi k r 0 0 σ Bs).toReal := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set y1 := midB r 0 (Matrix.of h) with hy1
  set y1' := midB r 0 (Matrix.of h') with hy1'
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := by rw [← hz]; exact hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := by rw [← hz']; exact hh'
  have hy1W : y1 ∈ UWset k 0 z0 := uw_mid r 0 z0 _ hhL
  have hy1W' : y1' ∈ UWset k 0 z0' := uw_mid r 0 z0' _ hhL'
  have uy1 : IsUnit y1.det := gv_unit hy1W.1
  have uy1' : IsUnit y1'.det := gv_unit hy1W'.1
  have hγ' : y1⁻¹ * γ0 * y1' ∈ B.GV k 0 := by
    have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k 0
    exact hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hy1W.1) _ hγ0) _ hy1W'.1
  have hAUT : ∀ x, Amat σ d x ∈ C2.UTset r := conjS_UT hd
  have hAc : ∀ i j, Measurable fun x => Amat σ d x i j := fun i j => ((Amat_cont σ d).matrix_elem i j).measurable
  have hAi : ∀ i j, Measurable fun x => (Amat σ d x)⁻¹ i j :=
    fun i j => ((Amat_inv_cont σ d hd).matrix_elem i j).measurable
  have hmp := phiC_mp σ y1 y1' (Amat σ d) hAUT hAc hAi hy1W.1 hy1W'.1
  have hemb := phiC_emb σ y1 y1' (Amat σ d) hAUT hAc hAi uy1 uy1'
  set g : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) → (Wq →L[ℂ] Wp) := fun q =>
    theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2))) with hg
  set φ : U.Xi k r 0 0 σ → (Wq →L[ℂ] Wp) := fun ξ =>
    U.psiStar k 0 σ S.z S.z' ξ • F (U.gaXi k 0 σ d ξ (fun a => a.elim0) (y1⁻¹ * γ0 * y1')) with hφ
  have hcomp : g ∘ phiC σ y1 y1' (Amat σ d) = fun p => chiL σ.symm p.1 • conjL S h h' (φ p.2) := by
    funext p
    rw [conjL_apply]
    exact integrand_pw S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F h h' hh hh' p

  have hφc : Continuous φ := (psiStar_cont σ S.z S.z').smul (FgaX_cont σ d hd F hFc _ hγ')
  have hφb : ∀ ξ, ‖φ ξ‖ ≤ Bs.indicator (fun _ => M) ξ := by
    intro ξ
    rw [hφ, norm_smul, norm_psiStar, one_mul]
    exact hdom ξ _ hγ'
  have hφi : Integrable φ (U.muXi k r 0 0 σ) := by
    refine Integrable.mono' ((integrableOn_const (C := M) hBsf.ne).integrable_indicator hBs)
      hφc.aestronglyMeasurable (Filter.Eventually.of_forall hφb)
  have hGi : Integrable (fun ξ => conjL S h h' (φ ξ)) (U.muXi k r 0 0 σ) := (conjL S h h').integrable_comp hφi
  have hpi : Integrable (fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => chiL σ.symm p.1 • conjL S h h' (φ p.2))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ)) :=
    (chiL_integrable σ.symm).smul_prod hGi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmp.integrable_comp_emb hemb, hcomp]; exact hpi
  · rw [← hmp.integral_comp hemb g]
    change ∫ p, (g ∘ phiC σ y1 y1' (Amat σ d)) p ∂_ = _
    rw [hcomp]
    dsimp only
    rw [integral_prod_smul (chiL σ.symm) (fun ξ => conjL S h h' (φ ξ)), chiL_int, one_smul,
      (conjL S h h').integral_comp_comm hφi]
    rfl
  · have e1 := hmp.integral_comp hemb (fun q => ‖g q‖)
    rw [← e1]
    have e2 : (fun p => ‖g (phiC σ y1 y1' (Amat σ d) p)‖) = fun p => chiL σ.symm p.1 * ‖conjL S h h' (φ p.2)‖ := by
      funext p
      have := congrFun hcomp p
      simp only [Function.comp_apply] at this
      rw [this, norm_smul, Real.norm_of_nonneg (chiL_nonneg _ _)]
    rw [e2, integral_prod_mul (chiL σ.symm) (fun ξ => ‖conjL S h h' (φ ξ)‖), chiL_int, one_mul]
    calc ∫ ξ, ‖conjL S h h' (φ ξ)‖ ∂(U.muXi k r 0 0 σ) ≤ ∫ ξ, Bs.indicator (fun _ => M) ξ ∂(U.muXi k r 0 0 σ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((integrableOn_const (C := M) hBsf.ne).integrable_indicator hBs)
            (Filter.Eventually.of_forall fun ξ => (norm_conjL_le S h h' hh hh' _).trans (hφb ξ))
      _ = M * (U.muXi k r 0 0 σ Bs).toReal := by
          rw [integral_indicator hBs, setIntegral_const, smul_eq_mul, mul_comm, Measure.real]

end inner

end Formalism.FourierDecayAlt.P.PBM
