import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section embG

variable {k p ρ : ℕ}

theorem embG_mul (a b : B.Mat k ρ) : U.embG k p ρ (a * b) = U.embG k p ρ a * U.embG k p ρ b := by
  simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem embG_one' : U.embG k p ρ (1 : B.Mat k ρ) = 1 := by
  ext i j
  obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  simp only [Matrix.one_apply, (U.eB k p ρ).injective.eq_iff]
  simp only [U.embG, U.blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with (a | b) | c <;> rcases y with (a' | b') | c' <;> simp [Matrix.one_apply]

theorem embG_inv {a : B.Mat k ρ} (ha : IsUnit a.det) : U.embG k p ρ a⁻¹ = (U.embG k p ρ a)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← embG_mul, Matrix.nonsing_inv_mul _ ha, embG_one']

end embG

section muN

variable {k : ℕ}

def psiL (k p ρ : ℕ) (x : U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) : Mt k (p + ρ) :=
  Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1)

theorem psiL_cont (p ρ : ℕ) : Continuous (psiL k p ρ) := by
  unfold psiL
  exact (((Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp (continuous_snd.comp continuous_snd)).matrix_mul
    ((Formalism.FourierDecayAlt.P.Dx2.SplitF.mup_cont (k := k) p ρ).comp (continuous_fst.comp continuous_snd))).matrix_mul
    ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_fst)

theorem psiL_meas (p ρ : ℕ) : Measurable (psiL k p ρ) := by
  have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace ((G.UT p → ℂ) × Mt k ρ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) := Prod.borelSpace
  exact (psiL_cont p ρ).measurable

theorem unipotent_measure_left_invariant : MuNLeft := by
  intro k p ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite (volume : Measure (G.UT p → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  have hs := Formalism.FourierDecayAlt.P.Dx2.SplitF.split_all (k := k) p ρ
  have hinv := Formalism.FourierDecayAlt.P.haar_measure_inversion k (p + ρ) (Nset k (p + ρ)) (D.muN k (p + ρ))
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)) (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) (p + ρ))
  have hinvρ := Formalism.FourierDecayAlt.P.haar_measure_inversion k ρ (Nset k ρ) (D.muN k ρ)
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ) (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) ρ)
  set μ := (U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)) with hμ
  set T : U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) → U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) :=
    fun z => (-z.1, (Formalism.FourierDecayAlt.P.PBM.utInv p z.2.1, B2.invM z.2.2)) with hT
  have hTmp : MeasurePreserving T μ μ :=
    Formalism.FourierDecayAlt.P.PBM.negRC_mp.prod ((Formalism.FourierDecayAlt.P.PBM.utInv_mp p).prod ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas, hinvρ⟩)
  have hae : ∀ᵐ z ∂μ, (Matrix.of z.2.2 : B.Mat k ρ) ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae
      (Formalism.FourierDecayAlt.P.B5.haar_ae (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) ρ)))
  have hfun : (B2.invM ∘ Formalism.FourierDecayAlt.P.Dx2.SplitF.Psi k p ρ) =ᵐ[μ] (psiL k p ρ ∘ T) := by
    filter_upwards [hae] with z hz
    obtain ⟨x, q, y⟩ := z
    have hy : IsUnit (Matrix.of y : B.Mat k ρ).det := Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_unit (Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ) hz.1
    have hu : IsUnit (G.upper q).det := by
      rw [Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC.det_UT (Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
    show Matrix.of.symm ((Matrix.of (Matrix.of.symm (U.Rn k p ρ x * U.muP k p ρ (G.upper q) *
        U.embG k p ρ (Matrix.of y))))⁻¹) =
      Matrix.of.symm (U.embG k p ρ (Matrix.of (B2.invM y)) * U.muP k p ρ (G.upper (Formalism.FourierDecayAlt.P.PBM.utInv p q)) *
        U.Rn k p ρ (-x))
    rw [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Formalism.FourierDecayAlt.P.PBM.rn_inv,
      Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hu, Formalism.FourierDecayAlt.P.PBM.upper_utInv, ← embG_inv hy]
    simp only [Matrix.mul_assoc]
    rfl
  rw [← hinv, hs, Measure.map_map Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas (Formalism.FourierDecayAlt.P.Dx2.SplitF.psi_meas p ρ),
    Measure.map_congr hfun, ← Measure.map_map (psiL_meas p ρ) hTmp.measurable, hTmp.map_eq]
  rfl

end muN

section rc

variable {k p ρ : ℕ}

def actLin (y : B.Mat k ρ) : (Fin (2 * ρ + k + 1) → Fin p → ℂ) →ₗ[ℂ] (Fin (2 * ρ + k + 1) → Fin p → ℂ) where
  toFun c := fun v a => (y * Matrix.of c) v a
  map_add' c c' := by funext v a; rw [← Matrix.of_add_of, Matrix.mul_add]; rfl
  map_smul' t c := by funext v a; rw [← Matrix.smul_of, Matrix.mul_smul]; rfl

def swapL : (Fin (2 * ρ + k + 1) → Fin p → ℂ) ≃ₗ[ℂ] (Fin p → Fin (2 * ρ + k + 1) → ℂ) where
  toFun c := fun a v => c v a
  invFun c := fun v a => c a v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_actLin (y : B.Mat k ρ) : LinearMap.det (actLin (p := p) y) = y.det ^ p := by
  have e : actLin (p := p) y = (swapL (k := k) (ρ := ρ) (p := p)).symm.conj
      (LinearMap.pi fun a : Fin p => Matrix.toLin' y ∘ₗ LinearMap.proj a) := by
    apply LinearMap.ext
    intro c
    funext v a
    simp [actLin, swapL, LinearEquiv.conj_apply, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem rcAct_fst_mp (y : B.Mat k ρ) (hy : ‖y.det‖ = 1) :
    MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => fun v a => (y * Matrix.of c) v a) volume volume := by
  have := Formalism.FourierDecayAlt.P.HermitianFormFactor.isAddHaarMeasure_matrix_volume (A := Fin (2 * ρ + k + 1)) (B := Fin p)
  have hdet : LinearMap.det ((actLin (p := p) y).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, det_actLin, Algebra.norm_complex_apply, map_pow,
      Complex.normSq_eq_norm_sq, hy]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin (2 * ρ + k + 1) → Fin p → ℂ))
    (f := (actLin (p := p) y).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  exact ⟨(LinearMap.continuous_of_finiteDimensional ((actLin (p := p) y).restrictScalars ℝ)).measurable, h1⟩

theorem right_coset_action_measure_preserving : RcActMP := by
  intro k p ρ y hy
  unfold U.muRC
  rw [Measure.volume_eq_prod]
  exact (rcAct_fst_mp y hy).prod (MeasurePreserving.id _)

end rc

section right

theorem rcAct_cont {k p ρ : ℕ} :
    Continuous (fun q : Mt k ρ × U.RC k p ρ => rcAct (Matrix.of q.1) q.2) := by
  unfold rcAct
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    apply continuous_pi
    intro a
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  · fun_prop

theorem right_measure_preserving : RightMP := by
  intro k p ρ z' μj μ0' hH h1 hμ0
  have : IsFiniteMeasure μj := ⟨by rw [h1]; exact ENNReal.one_lt_top⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) (p + ρ)
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite (volume : Measure (G.UT p → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  have : IsFiniteMeasure μ0' := by rw [hμ0]; infer_instance

  have s1 := measurePreserving_prodAssoc μj (D.muN k ρ) ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))

  set g : Mt k ρ → Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ)) → U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) :=
    fun h' w => (rcAct (Matrix.of h') w.2.1, (w.2.2, w.1)) with hg
  have hgm : Measurable (Function.uncurry g) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ))) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × (Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ)))) := Prod.borelSpace
    have : BorelSpace ((G.UT p → ℂ) × Mt k ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) := Prod.borelSpace
    have hc : Continuous (Function.uncurry g) := by
      refine Continuous.prodMk ?_ ?_
      · exact rcAct_cont.comp (continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      · exact (continuous_snd.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)
    exact hc.measurable
  have hae : ∀ᵐ h' ∂μj, Measure.map (g h') ((D.muN k ρ).prod ((U.muRC k p ρ).prod volume)) =
      (U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hH] with h' hh'
    have hdet : ‖(Matrix.of h' : B.Mat k ρ).det‖ = 1 :=
      Formalism.FourierDecayAlt.P.HermitianFormFactor.det_norm_one (Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ) hh'.1
    have a1 := Measure.measurePreserving_swap (μ := D.muN k ρ) (ν := (U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))
    have a2 := measurePreserving_prodAssoc (U.muRC k p ρ) (volume : Measure (G.UT p → ℂ)) (D.muN k ρ)
    have a3 := (right_coset_action_measure_preserving k p ρ (Matrix.of h') hdet).prod
      (MeasurePreserving.id ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)))
    exact (a3.comp (a2.comp a1)).map_eq
  have s2 := (MeasurePreserving.id μj).skew_product hgm hae

  have hlev : MeasurePreserving (Formalism.FourierDecayAlt.P.PBM.levMt (k := k) p ρ rfl) μj μ0' :=
    ⟨(Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).measurable, hμ0.symm⟩
  have hN : MeasurePreserving (psiL k p ρ)
      ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))) (D.muN k (p + ρ)) :=
    ⟨psiL_meas p ρ, (unipotent_measure_left_invariant k p ρ).symm⟩
  have s3 := hlev.prod hN
  exact s3.comp (s2.comp s1)

end right

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
