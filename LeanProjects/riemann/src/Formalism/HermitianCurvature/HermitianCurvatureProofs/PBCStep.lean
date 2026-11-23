import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCHerg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

theorem norm_psiG (g : ℝ) (l c : ℂ) : ‖psiG g l c‖ = 1 := by
  simp only [psiG]
  rw [Complex.norm_exp]
  simp

theorem continuous_psiG (g : ℝ) (l : ℂ) : Continuous (psiG g l) := by
  unfold psiG
  fun_prop

theorem psi_prod (g : ℝ) (hg : g ≠ 0) (σ z : crystallineComparison.V f) :
    crystallineComparison.psi (σ * z) = ∏ v, psiG g ((g • σ) v) (z v) := by
  have key : ∀ v, (2 * (((g • σ) v) * z v).re / g : ℝ) = 2 * (σ v * z v).re := by
    intro v
    rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
    field_simp
  simp only [psiG, key]
  rw [← Complex.exp_sum, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair, Complex.ofReal_sum,
    Finset.mul_sum]

theorem integrable_mul_psiG {φ : ℂ → ℂ} (hφ : Integrable φ) (g : ℝ) (l : ℂ) :
    Integrable fun c => φ c * psiG g l c := by
  refine hφ.norm.mono' (hφ.aestronglyMeasurable.mul (continuous_psiG g l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun c => by rw [norm_mul, norm_psiG, mul_one]

theorem fourier_Nz (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : g ≠ 0) (dl : Fin f → ℝ)
    (hdl : ∀ v, dl v ≠ 0) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c) (σ : crystallineComparison.V f) :
    crystallineComparison.fourier (Nz Y κ D) σ = (∏ v, ((dl v : ℝ) : ℂ)) * Hh Y κ hat (g • σ) := by
  have hae : (fun z => ((Nz Y κ D z : ℝ) : ℂ) * crystallineComparison.psi (σ * z)) =ᵐ[volume]
      fun z => Fz Y κ D z * crystallineComparison.psi (σ * z) := by
    filter_upwards [ae_good] with z hz
    have h0 := Complex.nonneg_iff.mp (Fz_nonneg Y κ hκ D hD z hz)
    rw [Nz, if_pos hz]
    congr 1
    exact Complex.ext (by simp) (by simp [← h0.2])
  have hpt : ∀ z : crystallineComparison.V f, Fz Y κ D z * crystallineComparison.psi (σ * z) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v)) := by
    intro z
    rw [Fz, psi_prod g hg σ z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hone : ∀ v h h', ∫ c, D v h h' c * psiG g ((g • σ) v) c =
      ((dl v : ℝ) : ℂ) * hat v ((g • σ) v) h h' := by
    intro v h h'
    rw [hhat, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hdl v), one_mul]
  have hint : ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z : crystallineComparison.V f =>
      κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v))) := by
    intro h hh h' hh'
    exact (Integrable.fintype_prod (fun v => integrable_mul_psiG (hDi v h hh h' hh') g _)).const_mul _
  unfold crystallineComparison.fourier
  rw [integral_congr_ae hae]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun h hh => integrable_finsetSum _ (fun h' hh' => hint h hh h' hh')),
    Hh, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun h' hh' => hint h hh h' hh'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' hh' => ?_
  have hp := integral_fintype_prod_volume_eq_prod (fun v (c : ℂ) => D v h h' c * psiG g ((g • σ) v) c)
  rw [integral_const_mul, hp]
  simp_rw [hone]
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_good (τ : crystallineComparison.V f) : ∃ x : crystallineComparison.V f, Good x ∧ Good (x + τ) := by
  refine ⟨fun v => ((‖τ v‖ + 1 : ℝ) : ℂ), fun v => ?_, fun v => ?_⟩
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) ≠ 0
    have hpos : (0 : ℝ) < ‖τ v‖ + 1 := by positivity
    exact_mod_cast hpos.ne'
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) + τ v ≠ 0
    intro h
    have h2 : τ v = -(((‖τ v‖ + 1 : ℝ) : ℂ)) := by linear_combination h
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_neg] at h3
    rw [Complex.norm_of_nonneg (by positivity)] at h3
    linarith

theorem herglotz_germ (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ)
    (hG : GermData Y U P Q hat)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (Lm : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology Lm] [IsZLattice ℝ Lm]
    (hLm : ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm) (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V f, Good x → Good (x + g • σ) → ‖phi Y κ U x (x + g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  obtain ⟨LIM, hL⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists f Lm
  have hbd : ∀ σ ∈ crystallineComparison.dualSet La,
      ‖Hh Y κ hat (g • σ) + A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)‖ ≤ F σ := by
    intro σ hσ
    rw [← mean_split Lm.toAddSubgroup LIM hG κ hκ hL (g • σ)]
    refine Formalism.FourierDecayAlt.P.mean_bound_estimate _ LIM _ (F σ) hL.1 ?_
    intro x
    unfold phiG
    split_ifs with hx
    · exact hF σ hσ x hx.1 hx.2
    · obtain ⟨x0, h1, h2⟩ := exists_good (g • σ)
      simpa using (norm_nonneg _).trans (hF σ hσ x0 h1 h2)
  let A : crystallineComparison.V f → ℂ := fun σ => ((∏ v, dl v : ℝ) : ℂ) * A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) A := by
    intro T w hT
    have hinj : Set.InjOn (fun σ : crystallineComparison.V f => g • σ) T :=
      fun a _ b _ hab => smul_right_injective (crystallineComparison.V f) hgne hab
    have hT' : ∀ τ ∈ T.image (fun σ : crystallineComparison.V f => g • σ), τ ∈ Lm.toAddSubgroup := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact hLm σ (hT σ hσ)
    have h0 := limit_average_positive_definite Lm.toAddSubgroup LIM hG κ hκ hL.1 (T.image (fun σ : crystallineComparison.V f => g • σ)) hT'
      (fun τ => w (g⁻¹ • τ))
    simp_rw [Finset.sum_image hinj] at h0
    simp only [inv_smul_smul₀ hgne, ← smul_sub] at h0
    have hsplit : (∑ σ ∈ T, ∑ σ' ∈ T, A (σ - σ') * w σ * starRingEnd ℂ (w σ')) =
        ((∏ v, dl v : ℝ) : ℂ) * ∑ σ ∈ T, ∑ σ' ∈ T,
          A0 Lm.toAddSubgroup LIM Y κ U P Q (g • (σ - σ')) * w σ * starRingEnd ℂ (w σ') := by
      simp only [A, Finset.mul_sum, mul_assoc]
    rw [hsplit, Complex.re_ofReal_mul]
    exact mul_nonneg hc0 h0
  have hb : ∀ σ : crystallineComparison.dualSet La, ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [hfour]
    simp only [A]
    rw [← mul_add, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hbd σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) A (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

theorem herglotz_plain (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ‖Hh Y κ hat (g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) (0 : crystallineComparison.V f → ℂ) := by
    intro T w _
    simp
  have hb : ∀ σ : crystallineComparison.dualSet La,
      ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [Pi.zero_apply, add_zero, hfour, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hF σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) 0 (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

end

end Formalism.FourierDecayAlt.P.PBC
