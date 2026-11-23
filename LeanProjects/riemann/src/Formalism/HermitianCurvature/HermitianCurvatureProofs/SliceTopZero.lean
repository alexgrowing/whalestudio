import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
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
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
