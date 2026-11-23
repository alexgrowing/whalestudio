import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselDegree

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem haar_eq_smul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsUnit P.det)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hν : PI.BesselPeriodGGP.IsHaarOn (GG k r) ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (Formalism.REAL.muG ε).map (phi ε P) := by
  have hE := Formalism.REAL.isClosedEmbeddingMatrix
  have hC := Formalism.QuantumDeterminants.uHConj
  obtain ⟨hσ, h0, hconc, hleft⟩ := hν
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hme : MeasurableEmbedding (phi ε P) := hce.measurableEmbedding
  have hr := phi_range hE hC hP hH
  have h2 : (ν.comap (phi ε P)).map (phi ε P) = ν := by
    rw [hme.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hr]
    exact hconc
  have hsf : SigmaFinite (ν.comap (phi ε P)) :=
    SigmaFinite.of_map _ hm.aemeasurable (by rw [h2]; exact hσ)
  have hinv : (ν.comap (phi ε P)).IsMulLeftInvariant := ⟨fun u => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, hme.comap_apply, hme.comap_apply]
    have hu : Matrix.of (phi ε P u) ∈ GG k r := (phi_range_iff hE hC hP hH _).1 ⟨u, rfl⟩
    have h1 := hleft _ hu
    have hs' : MeasurableSet (phi ε P '' s) := hme.measurableSet_image.2 hs
    conv_rhs => rw [← h1, Measure.map_apply (lmul_cont _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : Formalism.QuantumDeterminants.lmulM (phi ε P u⁻¹) (Formalism.QuantumDeterminants.lmulM (phi ε P u) x) = x := by
        have h3 : (Matrix.of (phi ε P u⁻¹) : Mx k r) * Matrix.of (phi ε P u) = 1 := by
          have := lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Mx k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (phi ε P u⁻¹) : Mx k r) * (Matrix.of (phi ε P u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      rw [← lmul_phi hP, hx]; exact h2⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have e1 := Measure.haarMeasure_unique (ν.comap (phi ε P)) K
  have e2 := Measure.haarMeasure_unique (Formalism.REAL.muG ε) K
  have hb0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hbt : Formalism.REAL.muG ε K ≠ ∞ := K.isCompact.measure_lt_top.ne
  set a := (ν.comap (phi ε P)) K with ha
  set b := Formalism.REAL.muG ε K with hb
  have e3 : ν.comap (phi ε P) = (a / b) • Formalism.REAL.muG ε := by
    rw [e1, e2, smul_smul, ENNReal.div_mul_cancel hb0 hbt]
  have hc0 : a / b ≠ 0 := by
    intro h
    rw [h, zero_smul] at e3
    rw [e3, Measure.map_zero] at h2
    exact h0 h2.symm
  have hct : a / b ≠ ∞ := by
    intro h
    have hz : ∀ i, Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) = 0 := by
      intro i
      have h4 := measure_spanningSets_lt_top (ν.comap (phi ε P)) i
      have h5 : (ν.comap (phi ε P)) (spanningSets (ν.comap (phi ε P)) i) =
          ∞ * Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) := by
        have := congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m (spanningSets (ν.comap (phi ε P)) i)) e3
        simpa only [h, Measure.smul_apply, smul_eq_mul] using this
      by_contra hne
      rw [h5, ENNReal.top_mul hne] at h4
      exact lt_irrefl _ h4
    have h6 := measure_iUnion_null hz
    rw [iUnion_spanningSets] at h6
    exact hb0 (measure_mono_null (Set.subset_univ _) h6)
  refine ⟨a / b, hc0, hct, ?_⟩
  rw [← Measure.map_smul, ← e3, h2]

theorem schur_fdeg : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧ ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : HCFdegG := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := haar_eq_smul hP hH μG hμ
  obtain ⟨c, hc, hF⟩ := hHC k r ε ⟨Q, hQ⟩
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (phi ε Q) :=
    (phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ
  obtain ⟨hd, hS⟩ := hF mu R.H _ hR.3 hR.1 hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

end GlobalTheory.BesselDegree
