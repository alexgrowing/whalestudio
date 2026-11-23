import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLNf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

open Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section heads

theorem ptDiag_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (a : Fin (D.ptSize h)) : D.ptDiag h a ≠ 0 :=
  Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt

theorem zxH_det_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (v : XH h) : (zxH h j hh.2 v).det ≠ 0 := by
  unfold zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (ptDiag_ne hh))

theorem cdOn_mat {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m n : Type} [Fintype m] [Fintype n]
    {f : X → Matrix m n ℂ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b

theorem cd_lowW_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (a b : Fin p) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => U.lowW σ v a b) := by
  unfold U.lowW
  simp only [Matrix.add_apply, Matrix.of_apply]
  refine contDiff_const.add ?_
  split_ifs
  · exact contDiff_apply ℝ ℂ _
  · exact contDiff_const

theorem cd_zxH_entry (h : C.LPt) (j : ℕ) (hs : D.ptSize h = j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => zxH h j hs v a b) := by
  unfold zxH LeftFubiniLemmas.lhOf
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c' _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c'' _ => ContDiff.mul contDiff_const ?_
  exact cd_lowW_entry _ _ _

end heads

section curve

theorem cd_det {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) : ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => h (σ i) i)

theorem cd_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) (hd : ∀ x, (M x).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ ∞ (fun x => (M x)⁻¹ a b) := by
  have e : ∀ x, (M x)⁻¹ a b = ((M x).det)⁻¹ * (M x).adjugate a b := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ContDiff.mul ((cd_det M h).inv hd) ?_
  simp only [Matrix.adjugate_apply]
  refine cd_det _ fun c d => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact h _ _

theorem cd_zxHct_inv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => ((zxH h j hh.2 v)ᴴ)⁻¹ a b) := by
  refine cd_inv_entry (fun v => (zxH h j hh.2 v)ᴴ) (fun c d => ?_) (fun v => ?_) a b
  · simp only [Matrix.conjTranspose_apply]
    exact Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp (cd_zxH_entry h j hh.2 d c)
  · rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (zxH_det_ne hh v)

end curve

section curve2

theorem cd_zfull_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiff ℝ ∞ (fun q : XH h × ℂ => zfull (zxH h j hh.2 q.1) q.2 a b) := by
  simp only [zfull_apply]
  split_ifs
  · exact (cd_zxH_entry h j hh.2 _ _).comp contDiff_fst
  · exact contDiff_snd
  · exact contDiff_const

theorem cdOn_zfullInv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun q : XH h × ℂ => ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b) (Set.univ ×ˢ {τ | τ ≠ 0}) := by
  have e : ∀ q ∈ (Set.univ ×ˢ {τ : ℂ | τ ≠ 0} : Set (XH h × ℂ)),
      ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b = zfull ((zxH h j hh.2 q.1)ᴴ)⁻¹ (star q.2)⁻¹ a b := by
    intro q hq
    rw [zfull_conjTranspose_inv (zxH_det_ne hh q.1) hq.2]
  refine ContDiffOn.congr ?_ e
  simp only [zfull_apply]
  split_ifs
  · exact ((cd_zxHct_inv_entry h j hh _ _).comp contDiff_fst).contDiffOn
  · intro q hq
    have hτ : star q.2 ≠ 0 := star_ne_zero.2 hq.2
    have h1 := (contDiffAt_inv ℂ (n := ∞) hτ).restrict_scalars ℝ
    exact (h1.comp q ((Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp contDiff_snd).contDiffAt)).contDiffWithinAt
  · exact contDiffOn_const

theorem curveSmooth : CurveSmooth := by
  intro k r j hj h hh γ
  refine cdOn_mat fun p' q' => ?_
  obtain ⟨P, rfl⟩ := cast_eB_surj (k := k) hj p'
  obtain ⟨Q, rfl⟩ := cast_eB_surj (k := k) hj q'
  simp only [level_point_eq_block_three, LeftFubiniLemmas.castM_apply', Fin.cast_cast, Fin.cast_eq_self, Ux3.block3_apply]
  rcases P with ((a | a) | a) <;> rcases Q with ((b | b) | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply] <;>
    first
    | exact contDiffOn_const
    | (simp only [Matrix.mul_apply]
       refine ContDiffOn.sum fun c _ => ?_
       first
       | exact (cdOn_zfullInv_entry h j hh _ _).mul contDiffOn_const
       | exact contDiffOn_const.mul (cd_zfull_entry h j hh _ _).contDiffOn)

end curve2

section pts

theorem dmin_mMap_hi {k J ρ : ℕ} (z z' : Fin (2 * (J + ρ) + k + 1) → ℂ) (hz : inWb k (J + ρ) z)
    (hz' : inWb k (J + ρ) z') (Z : Matrix (Fin J) (Fin J) ℂ) (γ : B.Mat k ρ) (l : ℕ) (hl : l ≤ ρ + 1) :
    Dmin k (J + ρ) z z' (U.mMap k J ρ Z γ) ⟨J + l, by omega⟩ =
      Z.det * Dmin k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ ⟨l, by omega⟩ := by
  have hZ : Zhat k (J + ρ) z z' (U.mMap k J ρ Z γ) =
      Matrix.reindex (Ux3.eC J ρ) (Ux3.eC J ρ)
        (Matrix.fromBlocks Z 0 0 (Zhat k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 z z' hz hz', Formalism.QuantumDeterminants.Zhat_eq]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  unfold Dmin
  rw [hZ]
  exact Ux3.minor_blocks _ _ l hl _

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem dmin_castM' {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (l : ℕ)
    (hl : l < b + 2) :
    Dmin k b z z' (D.castM e g) ⟨l, hl⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨l, by omega⟩ := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem lowV_base {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {k r : ℕ} (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r)
    (e : j + 1 + (r - (j + 1)) = r) :
    U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z) = (T.bs (j + 1)).z ∧
      U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z') = (T.bs (j + 1)).z' := by
  unfold D.LevTower.base
  rw [← T.z_lev (j + 1) hj, ← T.z'_lev (j + 1) hj, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩
where
  castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
      D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
    subst h1 h2; rfl

theorem pts : Pts := by
  intro Wp Wq _ _ _ _ _ _ P p j hj h hh γ hγ hΩ v
  have hZ := zxH_det_ne hh v
  refine ⟨hZ, fun τ hτ => ?_⟩
  set Z := zxH h j hh.2 v
  have e : j + 1 + (P.r - (j + 1)) = P.r := by omega
  have hz := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
  have hz' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
  obtain ⟨hl1, hl2⟩ := lowV_base p.T j hj e
  have hdf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hx : x0 P.k P.r j hj Z τ γ = D.castM e (U.mMap P.k (j + 1) (P.r - (j + 1)) (zfull Z τ) γ) := rfl
  refine ⟨fun l hl1' hl2' => ?_, ?_⟩
  · by_cases hlj : l.val = j
    · have := (Formalism.FourierDecayAlt.P.CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' Z τ γ hZ hτ hγ).1
      have hl : l = ⟨j, by omega⟩ := Fin.ext hlj
      rw [hl, this]; exact hZ
    · obtain ⟨l', hl'⟩ : ∃ l', l.val = j + 1 + l' := ⟨l.val - (j + 1), by omega⟩
      have hl : l = ⟨j + 1 + l', by omega⟩ := Fin.ext hl'
      rw [hl, hx, dmin_castM' e, dmin_mMap_hi _ _ hz hz' _ _ l' (by omega), hl1, hl2]
      refine mul_ne_zero hdf ?_
      exact hΩ.1 ⟨l', by omega⟩ (by simp; omega)
  · rw [hx, gf_castM e]
    have hG := Formalism.FourierDecayAlt.P.level_function_slice P.k (j + 1) (P.r - (j + 1)) _ _ hz hz' 0 0 (zfull Z τ) γ
    rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG
    rw [hG, hl1, hl2]
    exact mul_pos (Complex.normSq_pos.2 hdf) hΩ.2

end pts

section head

theorem leading_block_of_base_point {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (e : r = j + (r - j)) : U.Zh k j (r - j) (D.castM e (x0 k r j hj Z τ γ)) = Z := by
  ext a b
  unfold U.Zh x0
  rw [LeftFubiniLemmas.castM_apply', LeftFubiniLemmas.castM_apply']
  simp only [Fin.cast_cast]
  have key : ∀ q : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1), q.val = 2 * (j + (r - j)) + k - a.val →
      q = U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    intro q hq; ext; rw [Ux3.block_index_last_val]; simp only [Fin.val_mk]; omega
  rw [key (Fin.cast _ _) (by simp), LeftFubiniLemmas.embedding_map_apply_last_block, dif_pos (by simp only [Fin.val_cast]; omega), zfull_apply,
    dif_pos (by simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk]; omega)]
  congr 1 <;> ext <;> simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk] <;> omega

end head

end Formalism.FourierDecayAlt.P.CutHB
