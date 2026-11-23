import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open Matrix

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
  (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
  (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)

theorem evD_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
  ext b t
  simp only [Matrix.map_apply, yMat, evD, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.eval_X, Matrix.submatrix_apply]
  rfl

theorem evD_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) := by
  ext a b
  simp only [Matrix.map_apply, dMat, evD, MvPolynomial.eval₂Hom_X', Matrix.submatrix_apply]

theorem zT_even (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = g (pos ⟨v, s⟩) := by
  rw [zT, Equiv.symm_apply_apply, if_neg hs]

theorem zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
  rw [zT, Equiv.symm_apply_apply, if_pos hs]

theorem adj_zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hg : (g (pos ⟨v, s⟩)).det ≠ 0) :
    (zT X D pos g (pos ⟨v, s⟩)).adjugate =
      (zT X D pos g (pos ⟨v, s⟩)).det • (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id := by
  set z := zT X D pos g (pos ⟨v, s⟩) with hz
  have hmul : z * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id = 1 := by
    rw [hz, zT_odd X D pos v s hs g]
    have h1 : ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id =
        (((g (pos ⟨v, s⟩))⁻¹).transpose * (g (pos ⟨v, s⟩)).transpose).submatrix id id :=
      Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _
    rw [h1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg)]
    simp
  have hdet : z.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← Matrix.inv_eq_right_inv hmul, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hdet, one_smul]

theorem evD_blockMats {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) :
    (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
      evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧
      (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') =
        ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧
      (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') =
        ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  intro hf _ v s
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, evD_yMat, ι.map_det]
    exact Matrix.det_submatrix_equiv_self (finCongr hN.2.symm) _
  · intro hs
    rw [dyMat, ← Matrix.submatrix_map, Matrix.map_mul, evD_yMat, evD_dMat, zT_even X D pos v s hs]
    rw [show ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) *
        ((f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) =
        ((d (pos ⟨v, s⟩)).map ι * (f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) from
      Matrix.submatrix_mul_equiv _ _ _ (finCongr hN.2.symm) _]
    rw [← Matrix.map_mul, Matrix.submatrix_submatrix, dfr, ← Matrix.submatrix_map, Matrix.submatrix_submatrix]
    ext a t
    rfl
  · intro hs
    have hz := hf (pos ⟨v, s⟩)
    have hY : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
        (((zT X D pos f' (pos ⟨v, s⟩)).det • (f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
      have h1 : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
          ((yMat X Kc j v s).map (evD X D pos ι hN d f')).adjugate := RingHom.map_adjugate _ _
      rw [h1, evD_yMat, ← adj_zT_odd X D pos v s hs f' hz]
      rw [show (((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm)).adjugate =
          ((zT X D pos f' (pos ⟨v, s⟩)).map ι).adjugate.submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) from
        Matrix.adjugate_submatrix_equiv_self (finCongr hN.2.symm) _]
      congr 1
      exact (RingHom.map_adjugate ι _).symm
    rw [YtMat, Matrix.map_mul, ← Matrix.submatrix_map, hY, Matrix.transpose_map, evD_dMat, Matrix.transpose_submatrix,
      Matrix.submatrix_submatrix]
    have hrev : ∀ t : Fin (NN X.G.P.m X.t j),
        Fin.rev (Fin.cast hN.2.symm (shiftI X j t)) = Fin.castLE (rk_le X D hN) (Fin.rev (Fin.cast hN.1.symm t)) := by
      intro t
      have h1 := hN.1
      have h2 := hN.2
      have h3 := rk_le X D hN
      have := t.isLt
      ext
      simp only [Fin.val_rev, Fin.coe_cast, Fin.coe_castLE, shiftI]
      omega
    ext t a
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Function.comp_apply, id, smul_eq_mul, dfr, map_mul, map_sum]
    rw [hrev, Finset.mul_sum]
    refine Fintype.sum_equiv (finCongr hN.2.symm) _ _ (fun b => ?_)
    simp only [finCongr_apply]
    ring

end GlobalTheory.TwV.DelA
