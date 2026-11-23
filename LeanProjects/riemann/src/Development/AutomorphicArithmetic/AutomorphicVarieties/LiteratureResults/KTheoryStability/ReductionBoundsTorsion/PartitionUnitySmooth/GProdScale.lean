import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.ReNonnegPsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DiagForm

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

section GNrmHelpers

set_option linter.unusedSectionVars false

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private def gP (h : HS L N) : ℝ := ∏ w : InfinitePlace L, ((mat h w).det.re) ^ w.mult

private theorem g_qR_single [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem g_cl_at {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [g_qR_single, g_qR_single] at this

private theorem g_qR_smul (c : ℝ) (h : HS L N) (z : VR L N) : qR (c • h) z = c * qR h z := by
  rw [← evR_apply, map_smul, evR_apply, smul_eq_mul]

private theorem g_det_pos {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) : 0 < (mat h w).det.re :=
  (Complex.pos_iff.1 (hh w).det_pos).1

private theorem g_gP_pos {h : HS L N} (hh : h ∈ Pos L N) : 0 < gP h :=
  Finset.prod_pos fun w _ => pow_pos (g_det_pos hh w) _

private theorem g_prod_scale (c : ℝ) (f : InfinitePlace L → ℝ) :
    ∏ w : InfinitePlace L, (c ^ N * f w) ^ w.mult = c ^ (N * Module.finrank ℚ L) * ∏ w, f w ^ w.mult := by
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul]

private theorem g_det_smul (r : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : (r • M).det.re = r ^ N * M.det.re := by
  have : r • M = (r : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [this, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private theorem g_gP_smul (r : ℝ) (h : HS L N) : gP (r • h) = r ^ (N * Module.finrank ℚ L) * gP h := by
  unfold gP
  simp only [mat_smul, g_det_smul]
  exact g_prod_scale r _

private theorem g_emb_val (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem g_ginv (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← g_emb_val, map_inv, Pi.inv_apply]

private theorem g_gP_ac (γ : Gm L N) (h : HS L N) : gP (actL (emb L N γ) h) = gP h := by
  unfold gP
  set u : L := algebraMap (𝓞 L) L ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).det with hu
  have hw : ∀ w : InfinitePlace L, (mat (actL (emb L N γ) h) w).det.re = w u ^ 2 * (mat h w).det.re := by
    intro w
    rw [mat_actL, g_ginv, det_mul, det_mul, det_conjTranspose]
    have e : (((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)).det = w.embedding u := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e]
    have e2 : star (w.embedding u) * (mat h w).det * w.embedding u =
        ((Complex.normSq (w.embedding u) : ℝ) : ℂ) * (mat h w).det := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
    rw [e2, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  simp only [hw, mul_pow, Finset.prod_mul_distrib]
  have hn : |Algebra.norm ℚ u| = 1 := by
    have := NumberField.Units.norm L (Matrix.GeneralLinearGroup.det (γ⁻¹ : Gm L N))
    simpa [hu, Matrix.GeneralLinearGroup.val_det_apply] using this
  have hu1 : ∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult = 1 := by
    rw [show (∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult) = (∏ w : InfinitePlace L, w u ^ w.mult) ^ 2 by
      rw [← Finset.prod_pow]; refine Finset.prod_congr rfl fun w _ => ?_; rw [← pow_mul, ← pow_mul, mul_comm]]
    rw [InfinitePlace.prod_eq_abs_norm]
    rw [hn, Rat.cast_one, one_pow]
  rw [hu1, one_mul]

private theorem g_ent (w : InfinitePlace L) (a b : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := by
  have e : (fun h : HS L N => mat h w a b) =
      (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
  rw [e]
  exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp (HSsub L N).subtypeL.contDiff

private theorem g_gP_cd : ContDiff ℝ (⊤ : ℕ∞) (gP : HS L N → ℝ) := by
  unfold gP
  refine contDiff_prod fun w _ => ContDiff.pow ?_ _
  have := Complex.reCLM.contDiff.comp (cd_det (k := (⊤ : ℕ∞)) (fun h : HS L N => mat h w) (fun i j => g_ent w i j))
  simpa [Function.comp_def] using this

end GNrmHelpers

theorem pf_GNrm : GNrm := by
  intro hB L _ _ N hN
  classical
  obtain ⟨-, -, -, h4, -, -⟩ := hB L N hN
  have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hNd : (0 : ℝ) < (N : ℝ) * (Module.finrank ℚ L : ℝ) := mul_pos (Nat.cast_pos.2 hN) (Nat.cast_pos.2 hd)
  set a : ℝ := ((N : ℝ) * (Module.finrank ℚ L : ℝ))⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hNd
  have hNa : ((N * Module.finrank ℚ L : ℕ) : ℝ) * a = 1 := by
    rw [ha, Nat.cast_mul, mul_inv_cancel₀ hNd.ne']
  have hpow : ∀ c : ℝ, 0 ≤ c → (c ^ (N * Module.finrank ℚ L)) ^ a = c := fun c hc => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, hNa, Real.rpow_one]
  refine ⟨fun h => (gP h ^ (-a)) • h, 3, by norm_num, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6⟩
  · have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun h : HS L N => gP h ^ (-a)) (Pos L N) := fun h hh =>
      ((g_gP_cd (L := L) (N := N)).contDiffAt.rpow_const_of_ne (g_gP_pos hh).ne').contDiffWithinAt
    exact hs.smul (contDiff_id.contDiffOn (s := Pos L N))
  · intro h hh
    exact ⟨_, Real.rpow_pos_of_pos (g_gP_pos hh) _, rfl⟩
  · intro γ h hh
    dsimp only
    rw [ac, ac, g_gP_ac, map_smul]
  · intro r hr h hh
    dsimp only
    rw [g_gP_smul, Real.mul_rpow (by positivity) (g_gP_pos hh).le, smul_smul]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_neg, hNa, Real.rpow_neg_one]
    field_simp
  · intro r hr h hh
    have hq : ∀ (c : ℝ) (k : HS L N) (y : Lat L N), q (c • k) y = c * q k y := fun c k y => by
      rw [← ev_apply, map_smul, ev_apply, smul_eq_mul]
    have hlam : ∀ (c : ℝ), 0 < c → ∀ k : HS L N, lam (c • k) = c * lam k := fun c hc k => by
      unfold lam
      simp only [hq]
      rw [Real.mul_iInf_of_nonneg hc.le]
    have hdual : dualH (r • h) = r⁻¹ • dualH h := HS_ext fun w => by
      simp only [dualH, mat_mkHS, mat_smul]
      have hdet : IsUnit (mat h w).det := (Matrix.isUnit_iff_isUnit_det _).1 (hh w).isUnit
      rw [Matrix.inv_eq_left_inv (B := r⁻¹ • (mat h w)⁻¹) (by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
          Matrix.nonsing_inv_mul _ hdet]), transpose_smul]
    unfold lamD
    rw [hdual, hlam r hr, hlam r⁻¹ (inv_pos.2 hr), mul_mul_mul_comm, mul_inv_cancel₀ hr.ne', one_mul]
  · intro δ hδ hδ4 h hh k hcl
    have hk : k ∈ Pos L N := (h4 δ hδ (by linarith) h hh k hcl).1
    have hat := fun w x => g_cl_at hcl w x
    have h1δ : 0 < 1 - δ := by linarith
    have hup : ∀ w, (mat k w).det.re ≤ (1 + δ) ^ N * (mat h w).det.re := fun w =>
      detMono _ _ (hh w) (hk w).posSemidef (1 + δ) (by linarith) (fun x => by
        have := (abs_le.1 (hat w x)).2; rw [add_mul, one_mul]; linarith)
    have hlo : ∀ w, (1 - δ) ^ N * (mat h w).det.re ≤ (mat k w).det.re := fun w => by
      have h0 := detMono _ _ (hk w) (hh w).posSemidef (1 - δ)⁻¹ (inv_pos.2 h1δ) (fun x => by
        rw [le_inv_mul_iff₀ h1δ]
        have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith)
      have := mul_le_mul_of_nonneg_left h0 (pow_nonneg h1δ.le N)
      rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h1δ.ne', one_pow, one_mul] at this
    have hPup : gP k ≤ (1 + δ) ^ (N * Module.finrank ℚ L) * gP h := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod (fun w _ => pow_nonneg (g_det_pos hk w).le _)
        (fun w _ => pow_le_pow_left₀ (g_det_pos hk w).le (hup w) _)
    have hPlo : (1 - δ) ^ (N * Module.finrank ℚ L) * gP h ≤ gP k := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod (fun w _ => pow_nonneg (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) _)
        (fun w _ => pow_le_pow_left₀ (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) (hlo w) _)
    have hPh := g_gP_pos hh
    have hPk := g_gP_pos hk
    have hA2 : gP k ^ a ≤ (1 + δ) * gP h ^ a := by
      have := Real.rpow_le_rpow hPk.le hPup ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ (by linarith)] at this
    have hA1 : (1 - δ) * gP h ^ a ≤ gP k ^ a := by
      have := Real.rpow_le_rpow (by positivity) hPlo ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ h1δ.le] at this
    intro z
    dsimp only
    rw [g_qR_smul, g_qR_smul, Real.rpow_neg hPk.le, Real.rpow_neg hPh.le]
    have hH : 0 ≤ qR h z := Finset.sum_nonneg fun w _ => re_nonneg_psd (hh w).posSemidef (z w)
    exact lipAlg δ _ _ _ _ hδ hδ4 (Real.rpow_pos_of_pos hPh a) hA1 hA2 hH (hcl z)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
