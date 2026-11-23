import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuBL

theorem trG_closedEmb' {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) :
    Topology.IsClosedEmbedding (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Formalism.QuantumDeterminants.Mt k r)) := by
  subst hn
  exact Formalism.L2.SG.Pf.WFL.cM_closedEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2

theorem haarG_B' {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r)
      ((Formalism.REAL.muG ε).map (fun γ => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Formalism.QuantumDeterminants.Mt k r))) := by
  have hSK := Formalism.L2.SG.Pf.Choice.haar_tr hn ε Q Qi h2 hg
  have hce := trG_closedEmb' hn ε h2
  obtain ⟨hz, hT1⟩ := Formalism.FourierDecayAlt.P.base_vector_exists k r
  have hT0 : 0 < Formalism.QuantumDeterminants.Tz k r (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) := by rw [hT1]; exact one_pos
  have hright := (quotient_measure_unitary_group k r _ hz hT0).2.2.2.1 _ hSK
  obtain ⟨hsf, hne, hcon, hleft⟩ := hSK
  refine ⟨hcon, hleft, hright, fun K hK => ?_, hne⟩
  rw [Measure.map_apply hce.measurable hK.isClosed.measurableSet]
  exact (hce.isCompact_preimage hK).measure_lt_top

def ReproTr : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r) μG →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, ‖σ g x‖ = ‖x‖) →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [NormedSpace ℂ Vp] (W : Formalism.FourierDecayAlt.B.Mat k r → Vp) (w : H)
    (y : Formalism.FourierDecayAlt.B.Mat k r), y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) →
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ (σ y w) (Matrix.of g) • (fun x => W (x * y)) (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ (σ y w)) (fun x => W (x * y)) x = W (x * y)

def L2RightTranslation : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
  ∀ (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS → Formalism.MainNotions.S.IsQuotMeas μG μS ν →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] (W : Formalism.FourierDecayAlt.B.Mat k r → Vp),
    ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) → (∀ x, x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → W x = 0) →
    (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖W (s * x)‖ = ‖W x‖) →
  ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l2SG ν (fun x => W (x * y)) = l2SG ν W

def GapOfHyp : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ τ : D.what₂.Tau,
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

section Facts

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

private theorem host_v_pos' (D : D7) : 0 < D.host.v := by
  have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos hd _
  unfold Formalism.BasicNotions.Host.v
  linarith

theorem theta_pos (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 < θ := by
  by_contra hθ
  push_neg at hθ
  have hv := host_v_pos' D
  have hq := C.nuS_q u τ
  unfold muNB kapN haarLie muS at hq
  simp (disch := exact mul_nonpos_of_nonneg_of_nonpos (by first | positivity | exact Real.rpow_nonneg (by linarith) _ | exact zpow_nonneg (by linarith) _) hθ) only [ENNReal.ofReal_of_nonpos, zero_smul, Measure.prod_zero, Measure.map_zero] at hq
  have hmeas : Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ)) := by
    apply Continuous.measurable
    unfold Formalism.L2.SG.RealObj.trG
    exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const
  have hpos : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) Set.univ ≠ 0 := by
    unfold Formalism.REAL.muG
    exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have h1 := hq (fun _ => 1) measurable_const
  simp only [lintegral_const, Measure.coe_zero, Pi.zero_apply, zero_mul, lintegral_zero, mul_one] at h1
  unfold muGB at h1
  rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at h1
  simp only [one_mul, mul_zero, zero_mul] at h1
  exact hpos h1

theorem sigB_rep (C : Choice X θ) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (sigB X (C.Q τ) (C.Qi τ) τ) ∧
      (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), ∀ x, ‖sigB X (C.Q τ) (C.Qi τ) τ g x‖ = ‖x‖) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨-, -, ⟨⟨hone, hmul⟩, hiso, -⟩, -⟩ := X.ds (vOf X τ)
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hB : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ, C.Qi τ * (C.Q τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmem : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) := by
    intro m hm
    have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
    show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ))
    calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
        = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C.Qi τ)ᴴ * (mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m) * C.Qi τ := by rw [h3]
      _ = (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ := by rw [hm']
      _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hA]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show X.B.σ (vOf X τ) (C.Q τ * 1 * C.Qi τ) = 1
    rw [Matrix.mul_one, h2, hone]
  · intro a ha b hb
    show X.B.σ (vOf X τ) (C.Q τ * (a * b) * C.Qi τ) =
      (X.B.σ (vOf X τ) (C.Q τ * a * C.Qi τ)).comp (X.B.σ (vOf X τ) (C.Q τ * b * C.Qi τ))
    rw [← hmul _ (hmem a ha) _ (hmem b hb)]
    rw [show C.Q τ * a * C.Qi τ * (C.Q τ * b * C.Qi τ) = C.Q τ * (a * b) * C.Qi τ by
      simp only [Matrix.mul_assoc, hB]]
  · intro g hg x
    exact hiso _ (hmem g hg) x

private theorem conj_mem_lemma (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    C.Qi τ * uMat γ * C.Q τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  have hγ : (uMat γ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := γ.2
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hB : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hC : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      (uMat γ)ᴴ * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (uMat γ * M)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]
  show (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) =
    Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [← h3]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hA, hB, hC]

theorem wT_off (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (hm : m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : wT C u τ m = 0 := by
  unfold wT
  rw [dif_neg]
  rintro ⟨γ, hγ⟩
  apply hm
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hA : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      C.Qi τ * (C.Q τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hm' : m = C.Qi τ * uMat γ * C.Q τ := by
    rw [hγ]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one, hA]
  rw [hm']
  exact conj_mem_lemma C τ γ

theorem wT_at (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    wT C u τ (C.Qi τ * uMat γ * C.Q τ) = X.Wloc u (vOf X τ) γ := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hB : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hex : ∃ γ' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ' = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ :=
    ⟨γ, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]⟩
  unfold wT
  rw [dif_pos hex]
  have heq : uMat hex.choose = uMat γ := by
    rw [hex.choose_spec]
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]
  have hc : hex.choose = γ := Subtype.ext (Units.ext heq)
  rw [hc]

end Facts

section Side

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def cS (D : D7) : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)

theorem cS_ne (D : D7) : cS D ≠ 0 := by
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka
    exact div_pos Real.pi_pos (host_v_pos' D)
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  unfold cS
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (mul_ne_zero two_ne_zero hka.ne') (mul_ne_zero hg0 hg1))

theorem conjUH (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    C.Qi τ * uMat γ * C.Q τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  exact conj_mem_lemma C τ γ

theorem norm_psi (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (m : Formalism.FourierDecayAlt.B.Mat k r) :
    ‖Formalism.QuantumDeterminants.psi k r z c m‖ = 1 := by
  simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]

theorem sideQ (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp) {C : Choice X θ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hLF : LocFactor C) (hCols : ∀ u τ, ColsTypeTr C u τ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.IsHCParam (lamD D τ) ∧
      IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) ∧
      Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧
      Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧
      cS D ≠ 0 ∧
      IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) ∧
      IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (C.muW u τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D θ) ∧
      Formalism.MainNotions.S.IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (muS (C.muW u τ) (muNB D θ)) (C.nuS u τ) ∧
      ContinuousOn (fun x => wT C u τ (x * C.y τ)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
      IsSPsiEquiv (zB X (C.Qi τ) u τ) (Formalism.QuantumDeterminants.psi D.R.k D.R.rS (zB X (C.Qi τ) u τ) (cS D))
        (piB X (C.Q τ) (C.Qi τ) u τ) (fun x => wT C u τ (x * C.y τ)) ∧
      (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
        Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
          eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) (Matrix.of g) •
            (fun x => wT C u τ (x * C.y τ)) (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
        rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ))
          (fun x => wT C u τ (x * C.y τ)) x = wT C u τ (x * C.y τ)) ∧
      l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) ≠ 0 ∧ l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  have hθ := theta_pos C u τ
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, hiso⟩ := sigB_rep C τ
  have hHG := haarTr C τ
  have hHGB := haarG_B' (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg
  have hty : IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) :=
    hCols u τ
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT hty
  have hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D θ) :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)
  have hmaps : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), x * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    fun x hx => Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models x (C.y τ) hx hy
  refine ⟨h, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hgap, hok, hz, hT, cS_ne D, hty, ?_, hHG,
    C.muW_haar u τ, hN, C.nuS_q u τ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hP, hmem⟩ := C.y_low τ
    refine ⟨P, hP, ?_, hmem⟩
    show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1
    have := hiso (C.y τ) hy (X.B.w (vOf X τ))
    rw [← hw1]
    exact this
  · exact hWc.comp (continuous_id.matrix_mul continuous_const).continuousOn hmaps
  · intro hh hhU m hm g hgU
    show wT C u τ (hh * m * g * C.y τ) = _ • _
    rw [show hh * m * g * C.y τ = hh * m * (g * C.y τ) by simp only [Matrix.mul_assoc]]
    exact hWe hh hhU m hm _ (hmaps g hgU)
  · exact hRT D.R.k D.R.rS _ hHGB _ _ hrep hiso _ _ _ _ hy hWr
  · have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
        ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
      rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
      rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, norm_psi, one_mul, hπ.2.1 h0 hh0]
    have heq := hL2 D.R.k D.R.rS _ hz hT _ _ _ hHG hSH (C.nuS_q u τ) _ (wT C u τ) hWc (wT_off C u τ) hinv (C.y τ) hy
    rw [heq]
    exact ⟨hne, hfin⟩

end Side

theorem wuBesselOfLoc {D : D7} {X : HidaSetting D} {θ : ℝ} (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (C : Choice X θ) : WuBesselOfLoc C := by
  unfold WuBesselOfLoc WuBessel
  intro hG hBW hLF hDS hHaar hCols u τ
  obtain ⟨h, hHC, hDSτ, hGap, hOK, hWb, hTz, hc, hType, hLow, hμG, hμW, hμN, hq, hcont, hspsi, hrep, hne, hlt⟩ :=
    sideQ hRT hL2 hGp hG hLF hCols u τ
  obtain ⟨B, hBm, hBW'⟩ := hBW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (cS D) (fun i => ((D.hcW u τ).u i : ℝ))
    (lamD D τ) (epsSH D.R) h (X.B.H (vOf X τ)) (sigB X (C.Q τ) (C.Qi τ) τ) hHC hDSτ hGap hOK hWb hTz hc
    (X.Vloc u (vOf X τ)) (piB X (C.Q τ) (C.Qi τ) u τ) hType (v0Of C τ) hLow
    (muGB X (C.Q τ) (C.Qi τ) τ) (C.muW u τ) (muNB D θ) (C.nuS u τ) hμG hμW hμN hq
    (fun x => wT C u τ (x * C.y τ)) hcont hspsi hrep hne hlt
  refine ⟨B, hBm, fun γ => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hd : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJJ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hd, Matrix.one_mul]
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hHinv : C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← h3]
    simp only [Matrix.mul_assoc, hA, hJJ, h1]
  obtain ⟨yi, hyi⟩ : ∃ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      M = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS :=
    ⟨_, rfl⟩
  have hyi1 : yi * C.y τ = 1 := by
    rw [hyi, show C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *
        C.y τ = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ *
        ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) by simp only [Matrix.mul_assoc], hy, hHinv]
  have hyi2 : C.y τ * yi = 1 := by
    first
      | exact mul_eq_one_comm.mp hyi1
      | exact (Matrix.mul_eq_one_comm (M := yi)).mp hyi1
      | (letI := Matrix.invertibleOfLeftInverse (C.y τ) yi hyi1; exact Matrix.mul_invOf_self (C.y τ))
  have hyiU : yiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * yi = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
    calc yiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * yi
        = yiᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * yi := by rw [hy]
      _ = (C.y τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * yi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
          rw [hyi2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmU : (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) =
      Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := conj_mem_lemma C τ γ
  have hxU : C.Qi τ * uMat γ * C.Q τ * yi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    show (C.Qi τ * uMat γ * C.Q τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ * yi) =
      Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc (C.Qi τ * uMat γ * C.Q τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ * yi)
        = yiᴴ * ((C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ)) * yi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [hmU, hyiU]
  have hxy : C.Qi τ * uMat γ * C.Q τ * yi * C.y τ = C.Qi τ * uMat γ * C.Q τ := by
    rw [Matrix.mul_assoc _ yi, hyi1, Matrix.mul_one]
  have hx' := hBW' _ hxU
  try simp only at hx'
  rw [hxy, wT_at] at hx'
  rw [hx']
  congr 1
  obtain ⟨⟨-, hmul⟩, -⟩ := sigB_rep C τ
  have hcomp := hmul _ hxU (C.y τ) (C.y_mem τ)
  rw [hxy] at hcomp
  unfold v0Of
  rw [show sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ * yi)
      (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) =
      sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ) (X.B.w (vOf X τ)) by rw [hcomp]; rfl]
  have hB2 : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  show X.B.σ (vOf X τ) (C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ) (X.B.w (vOf X τ)) =
    X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))
  rw [show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ by
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB2]]

end Formalism.L2.SG.Pf.WuBL
