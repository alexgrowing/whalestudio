import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section pw

variable {k r : ℕ}

theorem hMat_monoP (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : U.hMat σ d = C2.monoP σ.symm d := by
  ext i a
  simp only [U.hMat, U.wP, C2.monoP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : σ i = a
  · have h' : i = σ.symm a := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : ¬ i = σ.symm a := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    simp [h, h']

theorem headH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (v : U.LW σ → ℂ) (u : G.UT r → ℂ) :
    U.headH σ d v u = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) * C2.monoP σ.symm d * G.upper u := by
  have h := StabilizerDisintegration.UC.permutationMatrix_mul_lowerUnipotent (σ := σ) (fun q => v (StabilizerDisintegration.UC.iota σ q))
  simp only [Equiv.apply_symm_apply] at h
  rw [U.headH, h, Matrix.mul_assoc (StabilizerDisintegration.lowP σ.symm _) (U.wP σ), ← U.hMat, hMat_monoP]

theorem psiC_add (c x y : ℂ) : C2.psiC c (x + y) = C2.psiC c x * C2.psiC c y := by
  unfold C2.psiC
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Complex.add_re, Complex.ofReal_add]

theorem psiC_star_mul (c x : ℂ) : C2.psiC c x * star (C2.psiC c x) = 1 := by
  have key : ∀ t : ℝ, Complex.exp (Complex.I * t) * star (Complex.exp (Complex.I * t)) = 1 := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring, Complex.exp_zero]
  exact key _

end pw

section pwmain

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def Amat (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (x0 : C2.Lstidx σ.symm → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d

private theorem mul_mem_utset_of_mem {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · rw [hA.1 i l hl', zero_mul]
      · rw [hB.1 l i hl', mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem integrand_pw (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z')
    (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) :
    theta0 S.z σ.symm (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
        (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F
        (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
          (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) =
    chiL σ.symm p.1 • ((S.π (Matrix.of h)).comp
      ((U.psiStar k 0 σ S.z S.z' p.2 • F (U.gaXi k 0 σ d p.2 (fun a => a.elim0)
        ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')))).comp (S.π' (Matrix.of h')⁻¹))) := by
  obtain ⟨x0, ⟨⟨y, y'⟩, ⟨⟨a, b⟩, ⟨v, u⟩⟩⟩⟩ := p
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := hz ▸ hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := hz' ▸ hh'
  have hY := uw_mid r 0 z0 _ hhL
  have hY' := uw_mid r 0 z0' _ hhL'
  have hYu : IsUnit (midB r 0 (Matrix.of h)).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY.1
  have hY'u : IsUnit (midB r 0 (Matrix.of h')).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY'.1
  have hAm : Amat σ d x0 ∈ C2.UTset r := conjS_UT hd x0
  have hAmi : (Amat σ d x0)⁻¹ ∈ C2.UTset r := ut_inv_mem hAm
  have hup : G.upper u ∈ C2.UTset r := StabilizerDisintegration.UC.upper_mem u
  have hprod : (Amat σ d x0)⁻¹ * G.upper u ∈ C2.UTset r := mul_mem_utset_of_mem hAmi hup
  have hV' : G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = (Amat σ d x0)⁻¹ * G.upper u := ut_of_mem hprod
  have hAmu : IsUnit (Amat σ d x0).det := ut_det hAm
  have hZu : IsUnit (U.hMat σ d).det := by
    rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact (Formalism.FourierDecayAlt.P.Dx2.SL.isUnit_wP σ).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hd a))
  have hγ0u : IsUnit γ0.det := gv_unit hγ0
  have hmat : (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))))ᴴ * U.hMat σ d * G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = U.headH σ d v u := by
    rw [hMat_monoP, orbit_split hd, headH_eq, hV']
    show _ * _ * G.upper (StabilizerDisintegration.utc (Amat σ d x0 * ((Amat σ d x0)⁻¹ * G.upper u))) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAmu, Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  have hsgs : B.sgs ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) (U.mMap k r 0 (U.hMat σ d) γ0) =
      U.gaXi k 0 σ d ((y, y'), ((a, b), (v, u))) (fun a => a.elim0) ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) := by
    rw [sgs_formula z0 z0' h h' hhL hhL', rnAct_inv_rnAct hYu, rnAct_inv_rnAct hY'u, hmat, gaXi_zero]
  have hθ : theta0 S.z σ.symm ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = chiL σ.symm x0 := by
    simp only [theta0, psiR, Equiv.apply_symm_apply, blkU_uMap_muP_Rn, x0c, StabilizerDisintegration.UC.utc_upper]
    show chiL σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.eSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))).1 = chiL σ.symm x0
    rw [MeasurableEquiv.symm_apply_apply]
  have hUU : ∀ w : G.UT r → ℂ, Formalism.DoubleCosetMeasures.IsUpUni (G.upper w) := fun w =>
    ⟨fun i j hij => (StabilizerDisintegration.UC.upper_mem w).1 i j hij, (StabilizerDisintegration.UC.upper_mem w).2⟩
  have hr1 : psi k r S.z cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h)) y)) = psi k r S.z cStd (U.Rn k r 0 y) := by
    have e := psi_rnAct z0 cStd _ hY (rnAct (midB r 0 (Matrix.of h)) y)
    rw [rnAct_inv_rnAct hYu] at e
    rw [hz]
    exact e.symm
  have hr2 : psi k r S.z' cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h')) y')) = psi k r S.z' cStd (U.Rn k r 0 y') := by
    have e := psi_rnAct z0' cStd _ hY' (rnAct (midB r 0 (Matrix.of h')) y')
    rw [rnAct_inv_rnAct hY'u] at e
    rw [hz']
    exact e.symm
  have hs1 : C2.simpleUp (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))) = C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ +
      C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ := by
    rw [StabilizerDisintegration.UC.upper_fSp]
    exact simpleUp_mul (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1)
      (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowerUnipotent_mem σ.symm _).1)
  have hs2 : C2.simpleUp (G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) = C2.simpleUp (Amat σ d x0)⁻¹ + C2.simpleUp (G.upper u) := by
    rw [hV']
    exact simpleUp_mul hAmi hup
  have hMu : IsUnit (C2.monoP σ.symm d).det := hMat_monoP σ d ▸ hZu
  have hinv : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d = (Amat σ d x0)⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose, hMat_monoP]
    show _ = ((C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    simp only [Matrix.mul_assoc]
  have hrelU : C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ) =
      C2.psiC cStd (C2.simpleUp (Amat σ d x0)⁻¹) := by
    have hQ : (StabilizerDisintegration.lowS σ.symm x0)ᴴ ∈ C2.UTset r := StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1
    have hQ' : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d ∈ C2.UTset r := by
      rw [hinv]
      exact hAmi
    rw [relevance_U S (U.hMat σ d) hZu γ0 hγ0u hrel _ hQ hQ', hinv]
  have hw : U.wP σ * U.lowW σ v * (U.wP σ)⁻¹ = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) := by
    have e := StabilizerDisintegration.UC.conj_lowW σ (fun q => v (StabilizerDisintegration.UC.iota σ q))
    simp only [Equiv.apply_symm_apply] at e
    exact e
  have hright : G.psi U.betaU (U.subS (U.wP σ * U.lowW σ v * (U.wP σ)⁻¹) + U.supS (G.upper u)) =
      C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) := by
    rw [StabilizerDisintegration.UC.psi_conj, map_add, psiC_add, hw, ← StabilizerDisintegration.UC.subS_eq, ← StabilizerDisintegration.UC.psi_conj,
      StabilizerDisintegration.UC.psi_star, StabilizerDisintegration.UC.supS_eq]
  have hstar := psiC_star_mul cStd (C2.simpleUp (Amat σ d x0)⁻¹)
  have hxi : B.xiTau S (1, 1) ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = U.psiStar k 0 σ S.z S.z' ((y, y'), ((a, b), (v, u))) := by
    rw [xiTau_one, psiStar_zero]
    simp only [psiR, Equiv.apply_symm_apply]
    rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z S.z_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z' S.z'_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem, hr1, hr2, hs1, hs2, psiC_add, psiC_add, hrelU, hright,
      star_mul', star_mul']
    linear_combination (C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) *
      psi k r S.z cStd (U.Rn k r 0 y) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) *
      star (psi k r S.z' cStd (U.Rn k r 0 y'))) * hstar
  have hphi : phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) (x0, ((y, y'), ((a, b), (v, u)))) =
      ((rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))), (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) := rfl
  rw [hphi]
  dsimp only
  rw [show TN k r ((h, (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) from rfl,
    D.orbIntegrand, B.rho]
  dsimp only
  rw [hθ, hxi, hsgs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end pwmain

end Formalism.FourierDecayAlt.P.PBM
