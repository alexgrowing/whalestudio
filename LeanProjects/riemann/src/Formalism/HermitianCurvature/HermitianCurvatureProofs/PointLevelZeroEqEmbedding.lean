import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhsInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section zero

variable {k ρ : ℕ}

theorem block_three_zero_size_eq {n : ℕ} (e : 0 + ρ = n) (A11 : Matrix (Fin 0) (Fin 0) ℂ)
    (A12 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin 0) (Fin 0) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ)
    (A31 : Matrix (Fin 0) (Fin 0) ℂ) (A32 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin 0) (Fin 0) ℂ) :
    D.castM e (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = D.castM (by omega : ρ = n) A22 := by
  subst e
  ext p q
  rw [LeftFubiniLemmas.castM_apply', LeftFubiniLemmas.castM_apply']
  have hp : (Fin.cast (by omega) p : Fin (2 * (0 + ρ) + k + 1)) = U.eB k 0 ρ (Sum.inl (Sum.inr (Fin.cast (by omega) p))) := by
    ext; rw [Ux3.block_index_middle_val]; simp
  have hq : (Fin.cast (by omega) q : Fin (2 * (0 + ρ) + k + 1)) = U.eB k 0 ρ (Sum.inl (Sum.inr (Fin.cast (by omega) q))) := by
    ext; rw [Ux3.block_index_middle_val]; simp
  rw [hp, hq, Ux3.block3_apply]
  simp

theorem castM_one {a b : ℕ} (h : a = b) : D.castM h (1 : B.Mat k a) = 1 := by
  subst h; exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl 1

theorem rn_zero0 (x : U.RC k 0 ρ) : U.Rn k 0 ρ x = 1 := by
  have h1 : D.castM (Nat.zero_add ρ) (U.Rn k 0 ρ x) = 1 := by
    unfold U.Rn
    rw [block_three_zero_size_eq]
    exact castM_one _
  have h2 := Formalism.FourierDecayAlt.P.PBH.asm_castM_symm (Nat.zero_add ρ) (U.Rn k 0 ρ x)
  rw [h1, castM_one] at h2
  exact h2.symm

theorem embG_zero0 {n : ℕ} (e : 0 + ρ = n) (y : B.Mat k ρ) :
    D.castM e (U.embG k 0 ρ y) = D.castM (by omega : ρ = n) y := by
  unfold U.embG
  exact block_three_zero_size_eq e _ _ _ _ _ _ _ _ _

end zero

section side

variable {k : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jf_left {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H (B.GV k r)) (g : B.Mat k r) (hg : g ∈ B.GV k r)
    (hI : Integrable (JF.integrand Bs H g) Bs.μSS) :
    B.JF Bs H g = ∫ x, psi k r Bs.z cStd (Matrix.of x.2) •
      (Bs.π (Matrix.of x.1)).comp (PBG.Kr Bs H ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * g)) ∂(Bs.μW.prod Bs.μN) := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW'
  have hint : ∀ P, JF.integrand Bs H g P = (1 : ℝ) • D.orbIntegrand Bs g H P := by
    intro P
    rw [one_smul]
    unfold JF.integrand D.orbIntegrand
    rw [VandermondePolynomialIntegral.xi11]
    rfl
  have hI1 : Integrable (fun P => (1 : ℝ) • D.orbIntegrand Bs g H P) Bs.μSS :=
    hI.congr (Filter.Eventually.of_forall hint)
  have hR : ∀ᵐ x ∂(Bs.μW.prod Bs.μN),
      Integrable (VandermondePolynomialIntegral.rint Bs H ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * g)) (Bs.μW'.prod Bs.μN) := by
    have hI' : Integrable (fun P => (1 : ℝ) • D.orbIntegrand Bs g H P)
        ((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)) := hI1
    have hgood : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
        (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
      have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
        Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
      have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
        Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
      filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩
    filter_upwards [hI'.prod_right_ae, hgood] with x hx hxg
    have hx0 : (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2)⁻¹ * g ∈ B.GV k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hxg.1.1)
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hxg.2.1)) hg
    refine Integrable.mono' hx.norm (VandermondePolynomialIntegral.rint_aesm Bs _ hx0 hHc) (Filter.Eventually.of_forall fun y => ?_)
    have hs := VandermondePolynomialIntegral.orb_split_pt Bs g (fun _ => 1) H x y
    show ‖VandermondePolynomialIntegral.rint Bs H _ y‖ ≤ ‖(1 : ℝ) • D.orbIntegrand Bs g H (x, y)‖
    rw [hs, norm_smul, norm_mul, VandermondePolynomialIntegral.norm_psi]
    simp only [Complex.ofReal_one, norm_one, one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    rw [← Bs.π_unitary _ hxg.1 (VandermondePolynomialIntegral.rint Bs H _ y v)]
    exact ((Bs.π (Matrix.of x.1)).comp (VandermondePolynomialIntegral.rint Bs H _ y)).le_opNorm v
  have hfub := VandermondePolynomialIntegral.fub Bs g (fun _ => 1) (fun _ => rfl) H hI1 hR
  have hJ : B.JF Bs H g = ∫ P, JF.integrand Bs H g P ∂Bs.μSS := rfl
  rw [hJ, integral_congr_ae (Filter.Eventually.of_forall hint), hfub.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold VandermondePolynomialIntegral.lint
  simp only [Complex.ofReal_one, one_mul]

theorem muRC0_real (ρ : ℕ) : (U.muRC k 0 ρ).real Set.univ = 1 := by
  have : IsEmpty (G.UT 0) := ⟨fun q => Fin.elim0 q.1.1⟩
  unfold U.muRC
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem pbF_zero {ρ n : ℕ} (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : 0 + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (y : B.Mat k n) :
    PBQ.pbF Bj B0 e H y = ∫ q, psi k ρ Bj.z cStd (Matrix.of q.2) •
      (Bj.π (Matrix.of q.1)).comp
        (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of q.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.2)⁻¹) * y))
      ∂(Bj.μW.prod Bj.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) 0 ρ
  have hz := Bj.z_mem
  unfold PBQ.pbF PBQ.muXP
  have hae : (PBQ.pbI Bj B0 e H y) =ᵐ[(Bj.μW.prod Bj.μN).prod (U.muRC k 0 ρ)] fun x =>
      psi k ρ Bj.z cStd (Matrix.of x.1.2) • (Bj.π (Matrix.of x.1.1)).comp
        (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2)⁻¹) * y)) := by
    filter_upwards [PBQ.ae_goodP (p := 0) Bj] with x hx
    unfold PBQ.pbI PBQ.cP PBQ.sP
    rw [if_pos hx]
    simp only [rn_zero0, Matrix.one_mul, embG_zero0, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one (LeftFubiniLemmas.inWb_liftVec hz), mul_one]
  rw [integral_congr_ae hae]
  rw [integral_fun_fst (fun q : Mt k ρ × Mt k ρ => psi k ρ Bj.z cStd (Matrix.of q.2) • (Bj.π (Matrix.of q.1)).comp
    (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of q.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.2)⁻¹) * y))),
    muRC0_real, one_smul]

theorem point_level_zero_eq_embedding (P : M.Par) (hj : 0 + 1 ≤ P.r) (Z : Matrix (Fin 0) (Fin 0) ℂ) (τ : ℂ)
    (γ : B.Mat P.k (P.r - (0 + 1))) : LevelPointCoordinates.x0 P.k P.r 0 hj Z τ γ = LevelPointCoordinates.mLev P 0 hj τ γ := by
  have hz : LevelPointCoordinates.zfull Z τ = Matrix.of fun _ _ => τ := by
    ext i l
    rw [LevelPointCoordinates.zfull_apply]
    have hi : i.val = 0 := by have := i.isLt; omega
    have hl : l.val = 0 := by have := l.isLt; omega
    simp [hi]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.mLev
  rw [hz]

end side

section main

open Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

theorem jfZero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hj : 0 + 1 ≤ P.r) (γ : B.Mat P.k (P.r - (0 + 1))) (hγ : γ ∈ B.GV P.k (P.r - (0 + 1)))
    (hΩ : γ ∈ Q.OmPlus P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z') (τ : ℂ) (hτ : τ ≠ 0)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hH : KB.CptCoef p.T.base H) (Z : Matrix (Fin 0) (Fin 0) ℂ) :
    B.JF (p.T.bs 0) H (LevelPointCoordinates.mLev P 0 hj τ γ) =
      PBQ.pbF (p.T.bs 0) p.T.base (by omega : 0 + (P.r - 0) = P.r) H (LevelPointCoordinates.x0 P.k P.r 0 hj Z τ γ) := by
  have hg0 : LevelPointCoordinates.mLev P 0 hj τ γ ∈ JF.Om P.k (P.r - 0) (p.T.bs 0).z (p.T.bs 0).z' := by
    have hm := Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z'
      (p.T.bs (0 + 1)).z_mem (p.T.bs (0 + 1)).z'_mem τ hτ γ hγ hΩ
    have hm2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (0 + 1) + 1 = P.r - 0) _ _ _ hm
    rw [Formalism.FourierDecayAlt.P.PBH.castM_castM', Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV,
      ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T 0 hj, ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T 0 hj] at hm2
    exact hm2
  have hCpt : KB.CptCoef (p.T.bs 0) H := hH
  rw [jf_left (p.T.bs 0) H (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) _ hg0.1
    (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) H hCpt _ hg0), pbF_zero, point_level_zero_eq_embedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  beta_reduce
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rfl

theorem side0Zero_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Zero := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj0 hF hw hγ hΩ e τ hτ
  subst hj0
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil

  set H : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 (by omega) w e with hHdef
  have hG0 : KB.slv p.T F 0 (by omega) w [] hh.2 e = H := by
    funext y
    unfold KB.slv D.castF
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil P.k P.r _ _ p.T.base.z_mem p.T.base.z'_mem H _).trans ?_
    exact congrArg H (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
  have hCpt : KB.CptCoef (p.T.bs 0) H := hG0 ▸ Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 (by omega) w [] hh hF e

  have hg0 : LevelPointCoordinates.mLev P 0 hj τ γ ∈ JF.Om P.k (P.r - 0) (p.T.bs 0).z (p.T.bs 0).z' := by
    have hm := Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z'
      (p.T.bs (0 + 1)).z_mem (p.T.bs (0 + 1)).z'_mem τ hτ γ hγ hΩ
    have hm2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (0 + 1) + 1 = P.r - 0) _ _ _ hm
    rw [Formalism.FourierDecayAlt.P.PBH.castM_castM', Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV,
      ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T 0 hj, ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T 0 hj] at hm2
    exact hm2

  have hL := jf_left (p.T.bs 0) H (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) _ hg0.1
    (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) H hCpt _ hg0)
  rw [hG0, hL]

  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
  set x₀ : XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hone : ∫ v, ellH ([] : C.LPt) v (CutHB.phf p F 0 hj w [] hh.2 γ v e τ) =
      CutHB.phf p F 0 hj w [] hh.2 γ x₀ e τ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀, integral_dirac]
    unfold ellH
    have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
      unfold U.subS
      exact Finset.sum_of_isEmpty _
    rw [hs]
    simp [G.psi]
  rw [hone]

  obtain ⟨R, hRF⟩ := hF.2.1
  have hpts := hPts Wp Wq P p 0 hj [] hh γ hγ hΩ x₀
  have hy0D := hpts.2 τ hτ
  have hy0G := LevelPointCoordinates.x0_GV hj hpts.1 hτ hγ
  have hPW := hW P.k 0 (P.r - 0) P.r Wp Wq (p.T.bs 0) p.T.base (by omega) (p.T.z_lev 0 (Nat.zero_le _)).symm 0
    (Nat.zero_le _) F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg) (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)
    (fun g hg hgC => by
      by_contra h0
      exact hgC (hRF g hg h0))
    (domP P.k P.r 0 p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨0, by omega⟩ (le_refl _) (Nat.zero_le _))
    (hPr Wp Wq P p 0 (Nat.zero_le _) _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy0D hy0G
  unfold CutHB.phf pbT
  rw [hPW, pbF_zero, point_level_zero_eq_embedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  beta_reduce
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rfl

end main

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
