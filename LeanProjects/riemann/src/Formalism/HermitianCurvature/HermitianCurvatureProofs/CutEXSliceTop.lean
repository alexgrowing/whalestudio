import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceTopZero

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_integral_level_reduction (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))) volume ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  have hz1 : B0.z = liftVec k p ρ Bj.z := by rw [← hz, JCTx5.castV_rfl]
  have hz1' : B0.z' = liftVec k p ρ Bj.z' := by rw [← hz', JCTx5.castV_rfl]
  have hπ1 : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Dx2.MN.castM_rfl, Dx2.Tower.lev_eq_embG]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    refine hHc.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Ux3.zhDmin]
    exact hx.2
  obtain ⟨hi, heq⟩ := SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz1' hπ1 hW' hW0' hNj hN0 g hg H hHc' R hR
  refine ⟨?_, ?_⟩
  · simpa only [Dx2.MN.castM_rfl] using hi
  · rw [JCTx5.castV_rfl, JCTx5.castV_rfl, hz1, hz1']
    simp only [Dx2.MN.castM_rfl]
    exact heq

end gen

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_gen (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hG : B.CkOn ⊤ (B.GV P.k P.r) G) (R : ℝ) (hR : ∀ x ∈ B.GV P.k P.r, G x ≠ 0 → B.gN x ≤ R)
    (h : C.LPt) (j : ℕ) (hjr : j ≤ P.r) (hh : D.IsLocPt h j) (hj1 : 1 ≤ j) (γ : B.Mat P.k (P.r - j))
    (hOm : γ ∈ JF.Om P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z') :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ)))) ∧
    B.JF (p.T.bs j) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
      ∫ v, PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ))) := by
  obtain ⟨hh1, rfl⟩ := hh
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hzj := p.T.z_lev (D.ptSize h) hjr
  have hzj' := p.T.z'_lev (D.ptSize h) hjr
  have hπj : ∀ y, (p.T.bs (D.ptSize h)).π' y = p.T.base.π' (D.castM e (ιLev P.k _ _ y)) :=
    fun y => p.T.π'_lev _ hjr y
  obtain ⟨hWj, hW'j, hNj⟩ := p.hT (D.ptSize h) hjr
  obtain ⟨hW0, hW'0, hN0⟩ := p.hT 0 (Nat.zero_le _)
  have hW0' : p.T.base.μW' = (p.T.bs (D.ptSize h)).μW'.map (PBM.levMt (D.ptSize h) (P.r - D.ptSize h) e) :=
    PBM.haar_lev _ _ e _ _ hzj' _ _ p.T.base.haarW' (p.T.bs _).haarW' hW'0 hW'j
  have hGc : ContinuousOn G {x | x ∈ B.GV P.k P.r ∧
      Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    (PBE.ckOn_continuousOn' subset_rfl hG).mono fun x hx => hx.1
  obtain ⟨H1i, H1e⟩ := slice_integral_level_reduction e hj1 (D.ptPerm h) (D.ptDiag h) (CutHB.ptDiag_ne ⟨hh1, rfl⟩)
    (p.T.bs (D.ptSize h)) p.T.base hzj hzj' hπj hW'j hW0' hNj hN0 γ hOm G hGc R hR
  have hcf : ∀ (e' : P.r - D.ptSize h = P.r - D.ptSize h) (F : B.Mat P.k (P.r - D.ptSize h) → (Wq →L[ℂ] Wp)),
      D.castF e' F = F := fun e' F => by
    funext x
    simp only [D.castF, Dx2.MN.castM_rfl]
  refine ⟨?_, ?_⟩
  · simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    simp only [SliceIntegralLemmas.psiH] at H1i
    exact H1i
  · rw [hcf, D.sliceAt, dif_pos hjr]
    simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact H1e

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  have h0 : ∀ (hl : 0 < 0 + 2), Dmin k 0 z z' γ ⟨0, hl⟩ = 1 := by
    intro hl
    simp [Dmin]
  have h1 : Dmin k 0 z z' γ (Fin.last (0 + 1)) = Q.zetaL k 0 z z' (Fin.last 0) γ := by
    rw [PBI.zetaL_eq_zhat]
    simp [Dmin, Matrix.det_unique]
  refine ⟨hγ, ?_, ?_⟩
  · intro l hl
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simpa using hl)
    rw [hl0, h0]
    exact one_ne_zero
  · unfold Gf
    rw [h1, h0]
    simpa [Q.GGl] using hG

end top

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem sliceTop_pos (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : 1 ≤ P.r) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm : γ ∈ JF.Om P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' :=
    om_zero (Nat.sub_self _) _ _ γ hγ hGG
  obtain ⟨R, hR⟩ := hG.1.2.1
  exact slice_gen P p G hG.1.1 R hR h P.r le_rfl hh hr γ hOm

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P

theorem slice_top_exhaustion : CutEX.SliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh γ hγ hGG
  rcases Nat.eq_zero_or_pos P.r with h0 | h1
  · exact CutEXSl0.sliceTop_zero Wp Wq P p h0 G hG h hh γ hγ hGG
  · exact CutEXSlice.sliceTop_pos Wp Wq P p h1 G hG h hh γ hγ hGG

end Formalism.FourierDecayAlt.P
