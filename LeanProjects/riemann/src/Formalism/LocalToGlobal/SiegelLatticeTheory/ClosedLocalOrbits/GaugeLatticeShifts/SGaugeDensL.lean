import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

section LogChart

open scoped Matrix.Norms.Operator

abbrev MxC (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

theorem hasStrict_expM :
    HasStrictFDerivAt (fun X : MxC n => NormedSpace.exp X)
      ((ContinuousLinearEquiv.refl ℝ (MxC n) : MxC n ≃L[ℝ] MxC n) : MxC n →L[ℝ] MxC n) 0 := by
  exact hasStrictFDerivAt_exp_zero

def eX (n : ℕ) : OpenPartialHomeomorph (MxC n) (MxC n) := (hasStrict_expM (n := n)).toOpenPartialHomeomorph _

theorem eX_apply (X : MxC n) : eX n X = NormedSpace.exp X := rfl

theorem zero_mem_eX : (0 : MxC n) ∈ (eX n).source := hasStrict_expM.mem_toOpenPartialHomeomorph_source

def logM (n : ℕ) : MxC n → MxC n := (eX n).symm

def invD (n : ℕ) : Set (MxC n) :=
  (fun X => fderiv ℝ (fun Y : MxC n => NormedSpace.exp Y) X) ⁻¹' Set.range ((↑) : (MxC n ≃L[ℝ] MxC n) → MxC n →L[ℝ] MxC n)

theorem isOpen_invD : IsOpen (invD n) :=
  ContinuousLinearEquiv.isOpen.preimage ((contDiff_expM (n := n)).continuous_fderiv (by simp))

theorem zero_mem_invD : (0 : MxC n) ∈ invD n :=
  ⟨ContinuousLinearEquiv.refl ℝ (MxC n), hasStrict_expM.hasFDerivAt.fderiv.symm⟩

def fJ (ε : Fin n → Bool) (X : MxC n) : MxC n := -(Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)

theorem continuous_fJ (ε : Fin n → Bool) : Continuous (fJ ε) :=
  ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg

theorem fJ_zero (ε : Fin n → Bool) : fJ ε 0 = 0 := by simp [fJ]

def sOne (ε : Fin n → Bool) : Set (MxC n) := (eX n).source ∩ invD n ∩ fJ ε ⁻¹' (eX n).source

theorem isOpen_sOne (ε : Fin n → Bool) : IsOpen (sOne ε) :=
  ((eX n).open_source.inter isOpen_invD).inter ((eX n).open_source.preimage (continuous_fJ ε))

theorem zero_mem_sOne (ε : Fin n → Bool) : (0 : MxC n) ∈ sOne ε :=
  ⟨⟨zero_mem_eX, zero_mem_invD⟩, by show fJ ε 0 ∈ (eX n).source; rw [fJ_zero]; exact zero_mem_eX⟩

def tOne (ε : Fin n → Bool) : Set (MxC n) := (eX n).target ∩ logM n ⁻¹' sOne ε

theorem isOpen_tOne (ε : Fin n → Bool) : IsOpen (tOne ε) := (eX n).isOpen_inter_preimage_symm (isOpen_sOne ε)

theorem logM_exp {X : MxC n} (hX : X ∈ (eX n).source) : logM n (NormedSpace.exp X) = X := (eX n).left_inv hX

theorem exp_mem_tOne {ε : Fin n → Bool} {X : MxC n} (hX : X ∈ sOne ε) : NormedSpace.exp X ∈ tOne ε := by
  refine ⟨(eX n).map_source hX.1.1, ?_⟩
  show logM n (NormedSpace.exp X) ∈ sOne ε
  rw [logM_exp hX.1.1]; exact hX

theorem one_mem_tOne (ε : Fin n → Bool) : (1 : MxC n) ∈ tOne ε := by
  have := exp_mem_tOne (zero_mem_sOne ε); rwa [NormedSpace.exp_zero] at this

theorem logM_one : logM n 1 = 0 := by
  have := logM_exp (n := n) zero_mem_eX; rwa [NormedSpace.exp_zero] at this

theorem Jm_inv (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (Formalism.REAL.Jm_mul_self ε)

theorem exp_fJ {ε : Fin n → Bool} {X : MxC n} (h : Formalism.REAL.inUJ ε (NormedSpace.exp X)) :
    NormedSpace.exp (fJ ε X) = NormedSpace.exp X := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hu : IsUnit (Formalism.REAL.Jm ε) := IsUnit.of_mul_eq_one _ hJ
  set y := NormedSpace.exp X with hy
  have e1 : fJ ε X = Formalism.REAL.Jm ε * (-Xᴴ) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Jm_inv, fJ, Matrix.mul_neg, Matrix.neg_mul]
  have e2 : ((yᴴ)⁻¹ : MxC n) = Formalism.REAL.Jm ε * y * Formalism.REAL.Jm ε := by
    apply Matrix.inv_eq_right_inv
    have h' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := h
    calc yᴴ * (Formalism.REAL.Jm ε * y * Formalism.REAL.Jm ε) = (yᴴ * Formalism.REAL.Jm ε * y) * Formalism.REAL.Jm ε := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h', hJ]
  rw [e1, Matrix.exp_conj _ _ hu, Matrix.exp_neg, Matrix.exp_conjTranspose, ← hy, e2, Jm_inv]
  calc Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * y * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε
      = (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * y * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by simp only [Matrix.mul_assoc]
    _ = y := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

theorem logM_inG {ε : Fin n → Bool} {y : MxC n} (hy : y ∈ tOne ε) (hU : Formalism.REAL.inUJ ε y) :
    Formalism.REAL.inG ε (logM n y) ∧ NormedSpace.exp (logM n y) = y := by
  have hX := hy.2
  have hexp : NormedSpace.exp (logM n y) = y := (eX n).right_inv hy.1
  refine ⟨?_, hexp⟩
  set X := logM n y with hXdef
  have hf : NormedSpace.exp (fJ ε X) = NormedSpace.exp X := exp_fJ (by rw [hexp]; exact hU)
  have heq : X = fJ ε X := (eX n).injOn hX.1.1 hX.2 (by rw [eX_apply, eX_apply, hf])
  have hJ := Formalism.REAL.Jm_mul_self ε
  show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
  have : Formalism.REAL.Jm ε * X = -(Xᴴ * Formalism.REAL.Jm ε) := by
    conv_lhs => rw [heq, fJ]
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  rw [this, add_neg_cancel]

def cM (ε : Fin n → Bool) : MxC n →L[ℝ] EL ε :=
  (((obG ε).repr.toContinuousLinearEquiv : gLie ε →L[ℝ] EL ε).comp (gLie ε).orthogonalProjectionOnto).comp
    (LinearMap.toContinuousLinearMap (realL n))

theorem cM_linT (ε : Fin n → Bool) (t : EL ε) : cM ε (linT ε t) = t := by
  simp only [cM, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  show (obG ε).repr ((gLie ε).orthogonalProjectionOnto (realV (linT ε t))) = t
  rw [linT_apply, realV_unrealify, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]

theorem realV_mem_of_inG {ε : Fin n → Bool} {X : MxC n} (h : Formalism.REAL.inG ε X) : realV X ∈ gLie ε :=
  Submodule.subset_span ⟨X, fun t => Formalism.REAL.exp_indefinite_unitary_holds n ε X h t, rfl⟩

theorem linT_cM {ε : Fin n → Bool} {X : MxC n} (h : Formalism.REAL.inG ε X) : linT ε (cM ε X) = X := by
  have hm := realV_mem_of_inG h
  have hc : cM ε X = (obG ε).repr ⟨realV X, hm⟩ := by
    show (obG ε).repr ((gLie ε).orthogonalProjectionOnto (realV X)) = _
    rw [show (gLie ε).orthogonalProjectionOnto (realV X) = ⟨realV X, hm⟩ from
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨realV X, hm⟩ : gLie ε)]
  rw [hc, linT_apply, LinearIsometryEquiv.symm_apply_apply]
  exact unrealify_realify X

theorem uMat_mul {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem inUJ_uMat {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (uMat g) := g.2

theorem expC_cM_logM {ε : Fin n → Bool} {g : Formalism.REAL.UJ ε} (hg : uMat g ∈ tOne ε) :
    expC ε (cM ε (logM n (uMat g))) = g := by
  obtain ⟨hG, hE⟩ := logM_inG hg (inUJ_uMat g)
  apply uMat_inj
  rw [uMat_expC, of_thetaExp, linT_cM hG, hE]

theorem chartNhd (ε : Fin n → Bool) : ChartNhd ε := by
  intro s hs
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing
  rw [hemb.nhds_eq_comap]
  have h1 : (((1 : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := rfl
  rw [h1]
  refine ⟨tOne ε ∩ logM n ⁻¹' (cM ε ⁻¹' Metric.ball 0 s), Filter.inter_mem ((isOpen_tOne ε).mem_nhds (one_mem_tOne ε)) ?_, ?_⟩
  · have hc : ContinuousAt (logM n) 1 := (eX n).continuousAt_symm (one_mem_tOne ε).1
    apply hc.preimage_mem_nhds
    rw [logM_one]
    apply (cM ε).continuous.continuousAt.preimage_mem_nhds
    rw [map_zero]
    exact Metric.ball_mem_nhds 0 hs
  · rintro g ⟨hg, hb⟩
    exact ⟨_, hb, expC_cM_logM hg⟩

theorem differentiableAt_logM {ε : Fin n → Bool} {y : MxC n} (hy : y ∈ tOne ε) :
    DifferentiableAt ℝ (logM n) y := by
  obtain ⟨L, hL⟩ := hy.2.1.2
  have hd : DifferentiableAt ℝ (fun Y : MxC n => NormedSpace.exp Y) ((eX n).symm y) :=
    (contDiff_expM (n := n)).differentiable (by simp) _
  have h2 : HasFDerivAt (eX n) (L : MxC n →L[ℝ] MxC n) ((eX n).symm y) := by
    have := hd.hasFDerivAt
    have hL' : (L : MxC n →L[ℝ] MxC n) = fderiv ℝ (fun Y : MxC n => NormedSpace.exp Y) ((eX n).symm y) := hL
    rw [← hL'] at this
    exact this
  exact ((eX n).hasFDerivAt_symm hy.1 h2).differentiableAt

theorem uMat_expC' (ε : Fin n → Bool) (t : EL ε) : uMat (expC ε t) = NormedSpace.exp (linT ε t) := by
  rw [uMat_expC, of_thetaExp]

theorem transC (ε : Fin n → Bool) : TransC ε := by
  have ho : IsOpen (linT ε ⁻¹' sOne ε) := (isOpen_sOne ε).preimage (linT ε).continuous
  have h0 : (0 : EL ε) ∈ linT ε ⁻¹' sOne ε := by
    show linT ε 0 ∈ sOne ε; rw [map_zero]; exact zero_mem_sOne ε
  obtain ⟨s₀, hs₀, hball⟩ := Metric.isOpen_iff.1 ho 0 h0
  refine ⟨s₀, hs₀, fun s hs hss z => ?_⟩
  let F : EL ε → MxC n := fun t => uMat z * NormedSpace.exp (linT ε t)
  have hFc : Continuous F := continuous_const.matrix_mul (continuous_expM.comp (linT ε).continuous)
  have hFd : ∀ t, DifferentiableAt ℝ F t := fun t =>
    (((contDiff_expM (n := n)).differentiable (by simp) _).comp t (linT ε).differentiableAt).const_mul _
  have hFu : ∀ t, F t = uMat (z * expC ε t) := fun t => by rw [uMat_mul, uMat_expC']
  refine ⟨F ⁻¹' tOne ε, (isOpen_tOne ε).preimage hFc, fun t => cM ε (logM n (F t)), ?_, ?_, ?_⟩
  · intro t ht
    exact ((cM ε).differentiableAt.comp t ((differentiableAt_logM ht).comp t (hFd t))).differentiableWithinAt
  · intro t ht
    have ht' : uMat (z * expC ε t) ∈ tOne ε := by rw [← hFu]; exact ht
    have h := logM_inG ht' (inUJ_uMat _)
    show Matrix.of (thetaExp ε (cM ε (logM n (F t)))) = _
    rw [of_thetaExp, hFu, linT_cM h.1, h.2, uMat_mul, uMat_expC]
  · rintro t ht ⟨t', ht', e'⟩
    have hS : linT ε t' ∈ sOne ε := hball (Metric.ball_subset_ball hss ht')
    have hF : F t = NormedSpace.exp (linT ε t') := by rw [hFu, ← e', uMat_expC']
    refine ⟨?_, ?_⟩
    · show F t ∈ tOne ε
      rw [hF]; exact exp_mem_tOne hS
    · show cM ε (logM n (F t)) ∈ _
      rw [hF, logM_exp hS.1.1, cM_linT]; exact ht'

end LogChart

end Formalism.MainNotions.S.Gauge
