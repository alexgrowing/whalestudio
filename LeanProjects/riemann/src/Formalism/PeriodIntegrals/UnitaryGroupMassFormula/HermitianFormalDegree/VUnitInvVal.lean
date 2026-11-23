import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeBoundOfHolomorphicContinuation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselSquareIntegrable.SchurHpk
import Formalism.PeriodIntegrals.HCFdeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeScaling.FdegScaleOf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace PI.UnitaryGroupMassFormula.FdegHpk

open PI.UpqRep

variable {n : ℕ}

theorem fdegOf_eq {ε : Fin n → Bool} (μ : Measure (UJ ε)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (w : H) (h : IsFdeg μ σ d) (hw : w ≠ 0) :
    fdegOf μ σ w = d := by
  unfold fdegOf
  obtain ⟨hd, hI⟩ := h
  obtain ⟨_, heq⟩ := hI w w w w
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h1 : ∀ g : UJ ε, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    first
    | (rw [RCLike.star_def, RCLike.mul_conj]; push_cast; rfl)
    | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl)
    | (rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl)
  simp_rw [h1] at heq
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at heq
  have key : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d := by
    have h2 : ((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (d : ℂ)) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      push_cast
      ring
    first
    | exact_mod_cast heq.trans h2
    | (apply Complex.ofReal_injective; rw [heq]; push_cast; ring)
    | (apply Complex.ofReal_injective; rw [heq, ← h2])
  rw [key]
  field_simp

section Scale

def vUnit {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  hP.unit * hP₂.unit⁻¹

theorem vUnit_val {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂) :
    ((vUnit hP hP₂ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = P * P₂⁻¹ := by
  simp [vUnit, Matrix.coe_units_inv]

theorem vUnit_inv_val {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂) :
    (((vUnit hP hP₂)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = P₂ * P⁻¹ := by
  simp [vUnit, _root_.mul_inv_rev, Matrix.coe_units_inv]

theorem vUnit_mem (ε : Fin n → Bool) {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂)
    (hJ : P₂ᴴ * Jm ε * P₂ = Pᴴ * Jm ε * P) : vUnit hP hP₂ ∈ UJ ε := by
  show inUJ ε ((vUnit hP hP₂ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  rw [vUnit_val]
  unfold inUJ
  have hd : IsUnit P₂.det := (Matrix.isUnit_iff_isUnit_det P₂).mp hP₂
  have h1 : P₂ * P₂⁻¹ = 1 := Matrix.mul_nonsing_inv P₂ hd
  have h2 : (P₂⁻¹)ᴴ * P₂ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (P * P₂⁻¹)ᴴ * Jm ε * (P * P₂⁻¹) = (P₂⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P₂⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (P₂⁻¹)ᴴ * P₂ᴴ * Jm ε * (P₂ * P₂⁻¹) := by rw [← hJ]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h2, h1, Matrix.one_mul, Matrix.mul_one]

def vU (ε : Fin n → Bool) {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂)
    (hJ : P₂ᴴ * Jm ε * P₂ = Pᴴ * Jm ε * P) : UJ ε :=
  ⟨vUnit hP hP₂, vUnit_mem ε hP hP₂ hJ⟩

theorem conjP_eq_conjP_conj (ε : Fin n → Bool) {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂)
    (hJ : P₂ᴴ * Jm ε * P₂ = Pᴴ * Jm ε * P) (g : UJ ε) :
    PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P₂ g = PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P (vU ε hP hP₂ hJ * g * (vU ε hP hP₂ hJ)⁻¹) := by
  unfold PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂
  congr 1
  have hP1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  simp [vU, toM, vUnit_val, vUnit_inv_val]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P₂).mp hP₂),
    ← Matrix.mul_assoc, hP1, Matrix.one_mul]
  rw [Matrix.mul_assoc _ P⁻¹ P, hP1, Matrix.mul_one]

theorem muG_conj (ε : Fin n → Bool) (v : UJ ε) : (muG ε).map (fun g => v * g * v⁻¹) = muG ε := by
  have h1 : (fun g : UJ ε => v * g * v⁻¹) = (fun g => g * v⁻¹) ∘ (fun g => v * g) := rfl
  rw [h1, ← Measure.map_map (continuous_mul_const v⁻¹).measurable (continuous_const_mul v).measurable,
    map_mul_left_eq_self]
  exact Formalism.REAL.indefinite_unitary_unimodular n ε v⁻¹

theorem scale_eq (ε : Fin n → Bool) {P P₂ : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hP₂ : IsUnit P₂)
    (hJ : P₂ᴴ * Jm ε * P₂ = Pᴴ * Jm ε * P) (c c₂ : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : (c • muG ε).map (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P) = (c₂ • muG ε).map (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P₂)) :
    c = c₂ := by
  have hfun : PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P₂ =
      PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P ∘ (fun g => vU ε hP hP₂ hJ * g * (vU ε hP hP₂ hJ)⁻¹) :=
    funext (conjP_eq_conjP_conj ε hP hP₂ hJ)
  have hE := PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_measurableEmbedding ε P hP
  have hcont : Continuous (fun g : UJ ε => vU ε hP hP₂ hJ * g * (vU ε hP hP₂ hJ)⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  rw [hfun, ← Measure.map_map hE.measurable hcont.measurable] at h
  simp only [Measure.map_smul, muG_conj] at h
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UJ ε)
  have hpos : 0 < muG ε K := Measure.measure_pos_of_mem_nhds (muG ε) hK1
  have hfin : muG ε K < ⊤ := hK.measure_lt_top
  have h2 := congrArg (fun m : Measure (Fin n → Fin n → ℂ) => m (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P '' K)) h
  simp only [hE.map_apply, Set.preimage_image_eq _ hE.injective, Measure.smul_apply, smul_eq_mul] at h2
  exact (ENNReal.mul_left_inj hpos.ne' hfin.ne).mp h2

end Scale

theorem fdegHpkHC_of (hHC : PI.HCFdeg) : Formalism.FourierDecayAlt.P.CutBP.Jmu.FdegHpkHC := by
  intro k r ε μG hG
  obtain ⟨cH, hcH, hH⟩ := hHC (2 * r + k + 1) ε
  have : SigmaFinite μG := hG.1
  have key : ∀ P, IsCayleyU k r ε P → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      μG = (c • muG ε).map (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P) := by
    intro P hP
    have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0 := by
      rw [hP.1.2]; exact hG.2.2.1
    have hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
      rw [hP.1.2]; intro s hs; exact hG.2.2.2 s hs
    exact PI.UnitaryGroupMassFormula.BesselL2FixAtZero.haar_transport ε P hP.1.1 μG hG.2.1 hconc hinv
  by_cases hex : ∃ P, IsCayleyU k r ε P
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam H _ _ _ σ w _ hds _
    obtain ⟨P, hP, -⟩ := hds
    exact absurd ⟨P, hP⟩ hex
  obtain ⟨P₀, hP₀⟩ := hex
  obtain ⟨c₀, hc0, hctop, hμ0⟩ := key P₀ hP₀
  refine ⟨cH / c₀.toReal, div_pos hcH (ENNReal.toReal_pos hc0 hctop), ?_⟩
  intro lam H _ _ _ σ w hl hds hw
  obtain ⟨P, hP, hDS⟩ := hds
  obtain ⟨c, -, hct, hμ⟩ := key P hP
  have hcc : c = c₀ := scale_eq ε hP.1.1 hP₀.1.1 (by rw [hP.1.2, hP₀.1.2]) c c₀ hct (hμ.symm.trans hμ0)
  have hF := hH lam H (fun g => σ (P⁻¹ * g * P)) hl hDS
  have hread := fdegOf_eq (muG ε) (fun g => σ (P⁻¹ * g * P)) _ w hF hw
  have hE := PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_measurableEmbedding ε P hP.1.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hμ, hE.integral_map, integral_smul_measure]
  have hfun : (fun g : UJ ε => ‖⟪w, σ (Matrix.of (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P g)) w⟫_ℂ‖ ^ 2) =
      fun g => ‖coefOn (ε := ε) (fun g => σ (P⁻¹ * g * P)) w w g‖ ^ 2 := rfl
  rw [hfun, hcc, smul_eq_mul, div_mul_eq_div_div_swap]
  unfold fdegOf at hread
  rw [hread]
  ring

end PI.UnitaryGroupMassFormula.FdegHpk
