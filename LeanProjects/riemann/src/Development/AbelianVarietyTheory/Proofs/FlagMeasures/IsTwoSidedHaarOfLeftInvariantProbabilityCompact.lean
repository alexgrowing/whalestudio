import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.JcRadialModuleFormOfParts

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
open scoped ENNReal

namespace GlobalTheory.ThA

private lemma measurable_lmulM_flag_measures {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))

private lemma measurable_rmulF' {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (B.rmulF a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private lemma measurableSet_lmulM_pair_mem {k r : ℕ} {A : Set (Mt k r)} (hA : MeasurableSet A) :
    MeasurableSet {p : Mt k r × Mt k r | lmulM (Matrix.of p.2) p.1 ∈ A} := by
  have hm : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hm hA

theorem measure_eq_smul_of_left_right {k r : ℕ} {U : Set (B.Mat k r)} {μ ν : Measure (Mt k r)}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ U) (hν : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ U)
    (hl : ∀ a ∈ U, Measure.map (lmulM a) μ = μ) (hr : ∀ a ∈ U, Measure.map (B.rmulF a) ν = ν) :
    ν = ν Set.univ • μ := by
  ext A hA
  set S : Set (Mt k r × Mt k r) := {p | lmulM (Matrix.of p.2) p.1 ∈ A} with hSdef
  have hS : MeasurableSet S := measurableSet_lmulM_pair_mem hA

  have hx : (μ.prod ν) S = ν A := by
    rw [Measure.prod_apply hS]
    have hslice : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) = ν A := by
      filter_upwards [hμ] with x hx
      have hpre : Prod.mk x ⁻¹' S = B.rmulF (Matrix.of x) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_rmulF' _) hA, hr _ hx]
    rw [lintegral_congr_ae hslice, lintegral_const, measure_univ, mul_one]

  have hy : (μ.prod ν) S = μ A * ν Set.univ := by
    rw [Measure.prod_apply_symm hS]
    have hslice : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' S) = μ A := by
      filter_upwards [hν] with y hy
      have hpre : (fun x => (x, y)) ⁻¹' S = lmulM (Matrix.of y) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_lmulM_flag_measures _) hA, hl _ hy]
    rw [lintegral_congr_ae hslice, lintegral_const]
  rw [Measure.smul_apply, smul_eq_mul, ← hx, hy, mul_comm]

theorem haarW_twoSided_of_left : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  intro k r z μ _ _ hH h1
  obtain ⟨_, hne, hconc, hleft⟩ := hH
  haveI : IsProbabilityMeasure μ := ⟨h1⟩
  have hinvU : ∀ g ∈ UWset k r z, g⁻¹ ∈ UWset k r z ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 :=
    fun g hg => Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
  have hUm : MeasurableSet {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} :=
    (show IsClosed {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} from
      Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z).measurableSet
  have hμU : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ UWset k r z := ae_iff.mpr hconc

  have hinvm : Measurable (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := Formalism.FourierDecayAlt.P.HermitianFormFactor.invF_meas
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure (Mt k r), ν = μ.map (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := ⟨_, rfl⟩
  have hmass : ν Set.univ = 1 := by
    rw [hνdef, Measure.map_apply hinvm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hνU : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ UWset k r z := by
    rw [hνdef]
    refine (ae_map_iff hinvm.aemeasurable hUm).2 ?_
    filter_upwards [hμU] with x hx using (hinvU _ hx).1

  have hνr : ∀ a ∈ UWset k r z, Measure.map (B.rmulF a) ν = ν := by
    intro a ha
    obtain ⟨hai, haa, -⟩ := hinvU a ha
    rw [hνdef, Measure.map_map (measurable_rmulF' a) hinvm]
    have hcomp : (B.rmulF a ∘ (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1)))) = (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) ∘ lmulM a⁻¹ := by
      funext x
      show ((Matrix.of x)⁻¹ * a : B.Mat k r) = (a⁻¹ * Matrix.of x)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv haa]
    rw [hcomp]
    exact (Measure.map_map hinvm (measurable_lmulM_flag_measures a⁻¹)).symm.trans (congrArg (Measure.map _) (hleft _ hai))
  have hkey := measure_eq_smul_of_left_right (μ := μ) (ν := ν) hμU hνU hleft hνr
  rw [hmass, one_smul] at hkey
  refine ⟨hconc, hleft, fun a ha => ?_, fun K _ => measure_lt_top μ K, hne⟩
  have h := hνr a ha
  rwa [hkey] at h

end GlobalTheory.ThA
